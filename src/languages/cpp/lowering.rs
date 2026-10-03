//! Direct lowering from the pinned C++ semantic artifact to kernel execution.
//!
//! This adapter consumes Clang's already-typed nodes. It does not print C++ as
//! C, invoke the C parser, or infer types from source spellings. The first
//! slice represents `int&` and `const int&` as address-valued kernel parameters;
//! every C++ lvalue-to-rvalue conversion becomes a typed load through that
//! address and assignment writes the referent without reseating the reference.
//! Mutable `int*` parameters remain distinct from references in the semantic
//! artifact, while both reuse the kernel's checked address and memory rules.
//! Function-body scalar locals use the kernel's ordinary declaration,
//! assignment, and call-result statements.

use std::collections::BTreeMap;

use super::{
    CppBinaryOperator, CppCallArgument, CppCleanup, CppConstant, CppExceptionBehavior,
    CppExpression, CppFieldReference, CppFunction, CppFunctionKind, CppInitializer, CppPlace,
    CppPlaceReference, CppRecord, CppStatement, CppType, PreparedCppImport,
};
use crate::kernel::{
    CAggregateField, CAggregateLayout, CExpression, CFunction, CStatement, CType, LoadSourceId,
    LoadSourceOwnerId, c_add, c_and, c_assign, c_begin_aggregate_construction, c_call,
    c_call_assign, c_cast, c_declare, c_declare_aggregate, c_divide, c_equal, c_function,
    c_greater_equal, c_greater_than, c_if, c_int32_literal, c_int64_literal, c_less_equal,
    c_less_than, c_multiply, c_parameter, c_pointer_offset_bytes, c_remainder, c_return, c_seq,
    c_skip, c_subtract, c_try_catch_int32, c_try_catch_int32_with_cleanup,
    c_typed_load_with_source, c_typed_store, c_uint32_literal, c_uint64_literal, c_variable,
};

/// One kernel function together with the immutable semantic artifact that
/// produced it. Keeping the source artifact attached retains Clang declaration
/// identities and spans even though they are not part of kernel equality.
#[derive(Clone, Debug)]
pub struct LoweredCppFunction {
    source: PreparedCppImport,
    function: CFunction,
    reachable_functions: Vec<CFunction>,
}

impl LoweredCppFunction {
    pub fn source(&self) -> &PreparedCppImport {
        &self.source
    }

    pub fn source_function(&self) -> &CppFunction {
        &self.source.export().function
    }

    pub fn kernel_function(&self) -> &CFunction {
        &self.function
    }

    pub fn reachable_kernel_functions(&self) -> &[CFunction] {
        &self.reachable_functions
    }
}

/// Lowers the first pinned C++ import slice directly to the kernel's checked
/// execution vocabulary.
pub fn lower_import(import: &PreparedCppImport) -> Result<LoweredCppFunction, String> {
    let function = lower_function(import, &import.export().function)?;
    let reachable_functions = import
        .export()
        .reachable_functions
        .iter()
        .map(|source| lower_function(import, source))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(LoweredCppFunction {
        source: import.clone(),
        function,
        reachable_functions,
    })
}

fn lower_function(import: &PreparedCppImport, source: &CppFunction) -> Result<CFunction, String> {
    let mut declared_places = Vec::new();
    collect_declared_places(&source.body, &mut declared_places);
    let places = source
        .parameters
        .iter()
        .chain(declared_places)
        .map(|parameter| (parameter.declaration_id.as_str(), parameter))
        .collect::<BTreeMap<_, _>>();
    let parameters = source
        .parameters
        .iter()
        .map(lower_parameter)
        .collect::<Result<Vec<_>, _>>()?;
    let mut context = LoweringContext {
        source_unit: import.logical_source(),
        function_name: &source.name,
        source_names: places.values().map(|place| place.name.as_str()).collect(),
        next_call_capture: 0,
        places,
        records: import
            .export()
            .records
            .iter()
            .map(|record| (record.declaration_id.as_str(), record))
            .collect(),
        constants: import
            .export()
            .constants
            .iter()
            .map(|constant| (constant.declaration_id.as_str(), constant))
            .collect(),
        next_load_occurrence: 0,
        return_capture_name: return_capture_name(source),
        nested_capture_name: fresh_internal_name(source, "__click_cpp_nested_value"),
        unwind_exception_name: fresh_internal_name(source, "__click_cpp_unwind_exception"),
        unwind_cleanups: matches!(
            import.export().exception_behavior,
            CppExceptionBehavior::ScalarInt32
        ),
    };
    let body = context.lower_function_body(&source.body)?;
    let return_type = match &source.function_kind {
        CppFunctionKind::Free
        | CppFunctionKind::StaticMethod { .. }
        | CppFunctionKind::Method { .. }
            if matches!(
                source.return_type,
                CppType::Integer {
                    bits: 32 | 64,
                    is_const: false,
                    ..
                }
            ) =>
        {
            cpp_scalar_kernel_type(&source.return_type)?
        }
        CppFunctionKind::Free
        | CppFunctionKind::StaticMethod { .. }
        | CppFunctionKind::Method { .. }
            if matches!(
                source.return_type,
                CppType::Boolean {
                    bits: 8,
                    is_const: false
                }
            ) =>
        {
            CType::Bool
        }
        CppFunctionKind::Free
        | CppFunctionKind::StaticMethod { .. }
        | CppFunctionKind::Method { .. }
            if source.return_type == CppType::Void =>
        {
            CType::Void
        }
        CppFunctionKind::Free
        | CppFunctionKind::StaticMethod { .. }
        | CppFunctionKind::Method { .. } => {
            return Err(format!(
                "C++ function `{}` has a return type outside direct lowering",
                source.name
            ));
        }
        CppFunctionKind::Constructor { .. } | CppFunctionKind::Destructor { .. } => CType::Void,
    };
    Ok(c_function(
        return_type,
        source.name.clone(),
        parameters,
        body,
    ))
}

fn lower_parameter(parameter: &CppPlace) -> Result<crate::kernel::CParameter, String> {
    match &parameter.value_type {
        CppType::Integer { .. } => Ok(c_parameter(
            parameter.name.clone(),
            cpp_scalar_kernel_type(&parameter.value_type)?,
        )),
        CppType::Boolean {
            bits: 8,
            is_const: false,
        } => Ok(c_parameter(parameter.name.clone(), CType::Bool)),
        CppType::LvalueReference { pointee }
            if is_mutable_int32(pointee) || is_const_int32(pointee) =>
        {
            Ok(c_parameter(parameter.name.clone(), CType::Int32Pointer)
                .with_pointee_constant(is_const_int32(pointee)))
        }
        CppType::LvalueReference { pointee } if is_const_int64(pointee) => Ok(c_parameter(
            parameter.name.clone(),
            CType::Int64Pointer,
        )
        .with_pointee_constant(true)),
        CppType::LvalueReference { pointee }
            if matches!(pointee.as_ref(), CppType::Record { .. }) =>
        {
            Ok(
                c_parameter(parameter.name.clone(), CType::Int32Pointer).with_pointee_constant(
                    matches!(pointee.as_ref(), CppType::Record { is_const: true, .. }),
                ),
            )
        }
        CppType::Pointer { pointee } if is_mutable_int32(pointee) => {
            Ok(c_parameter(parameter.name.clone(), CType::Int32Pointer))
        }
        _ => Err(format!(
            "C++ parameter `{}` is outside direct by-value `bool`, `int&`, `const int&`, `int*`, and record-reference lowering",
            parameter.name
        )),
    }
}

struct LoweringContext<'a> {
    source_unit: &'a str,
    function_name: &'a str,
    places: BTreeMap<&'a str, &'a CppPlace>,
    records: BTreeMap<&'a str, &'a CppRecord>,
    constants: BTreeMap<&'a str, &'a CppConstant>,
    next_load_occurrence: u32,
    return_capture_name: String,
    nested_capture_name: String,
    source_names: std::collections::BTreeSet<&'a str>,
    next_call_capture: u64,
    unwind_exception_name: String,
    unwind_cleanups: bool,
}

impl LoweringContext<'_> {
    /// Lowers the function body with its function-scope cleanup prefix on each
    /// operation that can propagate an exception. Return statements already
    /// carry their complete cleanup chain; this prefix is for calls and throws
    /// that escape the frame before a return is reached.
    fn lower_function_body(&mut self, statements: &[CppStatement]) -> Result<CStatement, String> {
        let function_cleanups = match statements.last() {
            Some(
                CppStatement::Return { cleanups, .. } | CppStatement::ReturnCall { cleanups, .. },
            ) => cleanups.as_slice(),
            _ => &[],
        };
        let mut active = Vec::new();
        let mut lowered = None;
        for statement in statements {
            let current = self.lower_statement_with_cleanups(statement, &active)?;
            lowered = Some(match lowered {
                Some(previous) => c_seq(previous, current),
                None => current,
            });
            if let CppStatement::Declare { local, .. } = statement
                && let Some(cleanup) = function_cleanups.iter().find(|cleanup| match cleanup {
                    CppCleanup::Destructor { object, .. } => {
                        object.declaration_id == local.declaration_id && object.name == local.name
                    }
                })
            {
                active.push(cleanup.clone());
            }
        }
        Ok(lowered.unwrap_or_else(c_skip))
    }

    fn lower_sequence(&mut self, statements: &[CppStatement]) -> Result<CStatement, String> {
        let mut statements = statements
            .iter()
            .map(|statement| self.lower_statement(statement));
        let Some(first) = statements.next() else {
            return Ok(c_skip());
        };
        let first = first?;
        statements.try_fold(first, |body, statement| {
            statement.map(|statement| c_seq(body, statement))
        })
    }

    fn lower_statement(&mut self, statement: &CppStatement) -> Result<CStatement, String> {
        match statement {
            CppStatement::Declare {
                local, initializer, ..
            } => match (&local.value_type, initializer) {
                (CppType::Integer { .. }, CppInitializer::Value { value }) => Ok(c_seq(
                    c_declare(
                        local.name.clone(),
                        cpp_scalar_kernel_type(&local.value_type)?,
                    ),
                    c_assign(local.name.clone(), self.lower_expression(value)?),
                )),
                (
                    CppType::Integer { .. },
                    CppInitializer::Call {
                        callee, arguments, ..
                    },
                ) => Ok(c_seq(
                    c_declare(
                        local.name.clone(),
                        cpp_scalar_kernel_type(&local.value_type)?,
                    ),
                    c_call_assign(
                        local.name.clone(),
                        callee.name.clone(),
                        self.lower_call_arguments(arguments)?,
                    ),
                )),
                (
                    CppType::Record {
                        declaration_id,
                        name,
                        ..
                    },
                    CppInitializer::Aggregate { fields, .. },
                ) => {
                    let record = self.records.get(declaration_id.as_str()).ok_or_else(|| {
                        format!("C++ lowering found unknown record declaration `{declaration_id}`")
                    })?;
                    if record.name != *name || fields.len() != record.fields.len() {
                        return Err(format!(
                            "C++ aggregate initializer for `{name}` disagrees with its record"
                        ));
                    }
                    let layout = cpp_record_layout(record)?;
                    let members = record
                        .fields
                        .iter()
                        .map(|field| {
                            Ok((
                                field.declaration_id.clone(),
                                field.offset_bytes,
                                cpp_scalar_kernel_type(&field.value_type)?,
                            ))
                        })
                        .collect::<Result<Vec<_>, String>>()?;
                    let mut result = c_declare_aggregate(local.name.clone(), layout);
                    for (initializer, (declaration_id, offset, value_type)) in
                        fields.iter().zip(members)
                    {
                        if initializer.field.declaration_id != declaration_id {
                            return Err(format!(
                                "C++ aggregate initializer for `{name}` is out of declaration order"
                            ));
                        }
                        let pointer =
                            c_pointer_offset_bytes(c_variable(local.name.clone()), offset);
                        let value = self.lower_expression(&initializer.value)?;
                        result = c_seq(result, c_typed_store(pointer, value, value_type));
                    }
                    Ok(result)
                }
                (
                    CppType::Record {
                        declaration_id,
                        name,
                        ..
                    },
                    CppInitializer::Constructor {
                        callee, arguments, ..
                    },
                ) => {
                    let record = self.records.get(declaration_id.as_str()).ok_or_else(|| {
                        format!("C++ lowering found unknown record declaration `{declaration_id}`")
                    })?;
                    if record.name != *name {
                        return Err(format!(
                            "C++ constructor initializer for `{name}` disagrees with its record"
                        ));
                    }
                    let layout = cpp_record_layout(record)?;
                    let mut lowered_arguments =
                        vec![c_cast(c_variable(local.name.clone()), CType::Int32Pointer)];
                    lowered_arguments.extend(self.lower_call_arguments(arguments)?);
                    Ok(c_seq(
                        c_begin_aggregate_construction(local.name.clone(), layout),
                        c_call(callee.name.clone(), lowered_arguments),
                    ))
                }
                _ => Err(format!(
                    "C++ local `{}` has an initializer outside direct lowering",
                    local.name
                )),
            },
            CppStatement::Assign { target, value, .. } => {
                let target_is_local =
                    matches!(self.place(target)?.value_type, CppType::Integer { .. });
                let value = self.lower_expression(value)?;
                if target_is_local {
                    Ok(c_assign(target.name.clone(), value))
                } else {
                    Ok(c_typed_store(
                        self.lower_place(target)?,
                        value,
                        CType::Int32,
                    ))
                }
            }
            CppStatement::Store { pointer, value, .. } => Ok(c_typed_store(
                self.lower_expression(pointer)?,
                self.lower_expression(value)?,
                CType::Int32,
            )),
            CppStatement::MemberStore {
                object,
                field,
                value,
                ..
            } => {
                let (pointer, value_type) = self.lower_member_pointer(object, field)?;
                Ok(c_typed_store(
                    pointer,
                    self.lower_expression(value)?,
                    value_type,
                ))
            }
            CppStatement::Return {
                value, cleanups, ..
            } => {
                let value_type = cpp_return_scalar_type(value.value_type())?;
                let value = self.lower_expression(value)?;
                if cleanups.is_empty() {
                    return Ok(c_return(value));
                }
                let capture = self.return_capture_name.clone();
                self.lower_captured_return(c_assign(capture, value), value_type, cleanups, false)
            }
            CppStatement::ReturnCall {
                callee,
                arguments,
                value_type,
                cleanups,
                ..
            } => {
                let capture = self.return_capture_name.clone();
                let (prefix, arguments) = self.lower_return_call_arguments(arguments)?;
                let call = c_seq(
                    prefix,
                    c_call_assign(capture, callee.name.clone(), arguments),
                );
                self.lower_captured_return(
                    call,
                    cpp_return_scalar_type(value_type)?,
                    cleanups,
                    true,
                )
            }
            CppStatement::Throw { value, .. } => {
                Ok(CStatement::Throw(self.lower_expression(value)?))
            }
            CppStatement::TryCatchInt32 {
                try_body,
                binding,
                handler,
                ..
            } => Ok(c_try_catch_int32(
                self.lower_sequence(try_body)?,
                binding.name.clone(),
                self.lower_sequence(handler)?,
            )),
            CppStatement::Scope { body, cleanups, .. } => {
                if self.unwind_cleanups && !cleanups.is_empty() {
                    if scope_needs_path_sensitive_unwind(body, cleanups) {
                        return self.lower_path_sensitive_scope(body, cleanups);
                    }
                    let Some((construction, live_body)) = body.split_first() else {
                        return Err("C++ unwind scope has no construction statement".into());
                    };
                    if !matches!(construction, CppStatement::Declare { .. }) {
                        return Err("C++ unwind scope must begin with guard construction".into());
                    }
                    let construction = self.lower_statement(construction)?;
                    let live_body = self.lower_sequence(live_body)?;
                    let binding = self.unwind_exception_name.clone();
                    let mut handler = c_skip();
                    for cleanup in cleanups {
                        handler = c_seq(handler, self.lower_cleanup(cleanup)?);
                    }
                    handler = c_seq(handler, CStatement::Throw(c_variable(binding.clone())));
                    let mut live_body =
                        c_try_catch_int32_with_cleanup(live_body, binding, handler, true);
                    for cleanup in cleanups {
                        live_body = c_seq(live_body, self.lower_cleanup(cleanup)?);
                    }
                    return Ok(c_seq(construction, live_body));
                }
                let mut result = self.lower_sequence(body)?;
                for cleanup in cleanups {
                    result = c_seq(result, self.lower_cleanup(cleanup)?);
                }
                Ok(result)
            }
            CppStatement::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                let condition = self.lower_expression(condition)?;
                let then_branch = self.lower_sequence(then_branch)?;
                let else_branch = self.lower_sequence(else_branch)?;
                Ok(c_if(condition, then_branch, else_branch))
            }
            CppStatement::Call {
                callee, arguments, ..
            } => Ok(c_call(
                callee.name.clone(),
                self.lower_call_arguments(arguments)?,
            )),
        }
    }

    /// Capture the result before destruction. A throwing return call takes the
    /// same cleanup chain on its exceptional edge and never produces a return.
    fn lower_captured_return(
        &mut self,
        mut evaluation: CStatement,
        value_type: CType,
        cleanups: &[CppCleanup],
        can_throw: bool,
    ) -> Result<CStatement, String> {
        let capture = self.return_capture_name.clone();
        if can_throw && self.unwind_cleanups && !cleanups.is_empty() {
            let binding = self.unwind_exception_name.clone();
            let mut handler = c_skip();
            for cleanup in cleanups {
                handler = c_seq(handler, self.lower_cleanup(cleanup)?);
            }
            handler = c_seq(handler, CStatement::Throw(c_variable(binding.clone())));
            evaluation = c_try_catch_int32_with_cleanup(evaluation, binding, handler, true);
        }
        let mut result = c_seq(c_declare(capture.clone(), value_type), evaluation);
        for cleanup in cleanups {
            result = c_seq(result, self.lower_cleanup(cleanup)?);
        }
        Ok(c_seq(result, c_return(c_variable(capture))))
    }

    /// Lowers a cleanup scope whose constructed-object set can differ by
    /// exceptional path. The ordinary scope shape has all declarations before
    /// the first potentially throwing operation, so it can use one checked
    /// cleanup edge around the live tail. Once a potentially throwing operation or initializer precedes a later
    /// declaration, that edge would incorrectly destroy an object that has not
    /// been constructed yet. Keep the active cleanup prefix while lowering
    /// each statement instead.
    fn lower_path_sensitive_scope(
        &mut self,
        body: &[CppStatement],
        cleanups: &[CppCleanup],
    ) -> Result<CStatement, String> {
        let mut active = Vec::new();
        let mut lowered = None;
        for statement in body {
            let current = self.lower_statement_with_cleanups(statement, &active)?;
            lowered = Some(match lowered {
                Some(previous) => c_seq(previous, current),
                None => current,
            });
            if let CppStatement::Declare { local, .. } = statement
                && let Some(cleanup) = cleanups.iter().find(|cleanup| match cleanup {
                    CppCleanup::Destructor { object, .. } => {
                        object.declaration_id == local.declaration_id && object.name == local.name
                    }
                })
            {
                active.push(cleanup.clone());
            }
        }
        let mut result = lowered.unwrap_or_else(c_skip);
        for cleanup in cleanups {
            result = c_seq(result, self.lower_cleanup(cleanup)?);
        }
        Ok(result)
    }

    /// Lowers one statement with the cleanup prefix that is alive on entry.
    /// Branches inherit the prefix, while a nested scope extends it only for
    /// the statements after its own construction.
    fn lower_statement_with_cleanups(
        &mut self,
        statement: &CppStatement,
        active: &[CppCleanup],
    ) -> Result<CStatement, String> {
        match statement {
            CppStatement::Declare {
                initializer: CppInitializer::Call { .. },
                ..
            } => {
                let declaration = self.lower_statement(statement)?;
                self.lower_throwing_statement(declaration, active)
            }
            CppStatement::Call {
                callee, arguments, ..
            } => {
                let call = c_call(callee.name.clone(), self.lower_call_arguments(arguments)?);
                self.lower_throwing_statement(call, active)
            }
            CppStatement::Throw { value, .. } => {
                let throw = CStatement::Throw(self.lower_expression(value)?);
                self.lower_throwing_statement(throw, active)
            }
            CppStatement::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                let condition = self.lower_expression(condition)?;
                let then_branch = self.lower_sequence_with_cleanups(then_branch, active)?;
                let else_branch = self.lower_sequence_with_cleanups(else_branch, active)?;
                Ok(c_if(condition, then_branch, else_branch))
            }
            CppStatement::TryCatchInt32 {
                try_body,
                binding,
                handler,
                ..
            } => Ok(c_try_catch_int32(
                self.lower_sequence_with_cleanups(try_body, active)?,
                binding.name.clone(),
                self.lower_sequence_with_cleanups(handler, active)?,
            )),
            CppStatement::Scope { body, cleanups, .. } => {
                let mut nested_active = active.to_vec();
                let mut lowered = None;
                for member in body {
                    let current = self.lower_statement_with_cleanups(member, &nested_active)?;
                    lowered = Some(match lowered {
                        Some(previous) => c_seq(previous, current),
                        None => current,
                    });
                    if let CppStatement::Declare { local, .. } = member
                        && let Some(cleanup) = cleanups.iter().find(|cleanup| match cleanup {
                            CppCleanup::Destructor { object, .. } => {
                                object.declaration_id == local.declaration_id
                                    && object.name == local.name
                            }
                        })
                    {
                        nested_active.push(cleanup.clone());
                    }
                }
                let mut result = lowered.unwrap_or_else(c_skip);
                for cleanup in cleanups {
                    result = c_seq(result, self.lower_cleanup(cleanup)?);
                }
                Ok(result)
            }
            _ => self.lower_statement(statement),
        }
    }

    fn lower_sequence_with_cleanups(
        &mut self,
        statements: &[CppStatement],
        active: &[CppCleanup],
    ) -> Result<CStatement, String> {
        let mut lowered = None;
        for statement in statements {
            let current = self.lower_statement_with_cleanups(statement, active)?;
            lowered = Some(match lowered {
                Some(previous) => c_seq(previous, current),
                None => current,
            });
        }
        Ok(lowered.unwrap_or_else(c_skip))
    }

    fn lower_throwing_statement(
        &mut self,
        statement: CStatement,
        active: &[CppCleanup],
    ) -> Result<CStatement, String> {
        if active.is_empty() {
            return Ok(statement);
        }
        let binding = self.unwind_exception_name.clone();
        let mut handler = c_skip();
        for cleanup in active.iter().rev() {
            handler = c_seq(handler, self.lower_cleanup(cleanup)?);
        }
        handler = c_seq(handler, CStatement::Throw(c_variable(binding.clone())));
        Ok(c_try_catch_int32_with_cleanup(
            statement, binding, handler, true,
        ))
    }

    fn lower_return_call_arguments(
        &mut self,
        arguments: &[CppCallArgument],
    ) -> Result<(CStatement, Vec<CExpression>), String> {
        let mut evaluation = c_skip();
        let mut lowered = Vec::with_capacity(arguments.len());
        for argument in arguments {
            crate::instrumentation::record_deterministic_work(1);
            if let CppCallArgument::Call {
                callee,
                arguments,
                value_type,
                ..
            } = argument
            {
                let (prefix, arguments) = self.lower_return_call_arguments(arguments)?;
                let capture = self.fresh_call_capture()?;
                evaluation = c_seq(
                    evaluation,
                    c_seq(
                        prefix,
                        c_seq(
                            c_declare(capture.clone(), cpp_return_scalar_type(value_type)?),
                            c_call_assign(capture.clone(), callee.name.clone(), arguments),
                        ),
                    ),
                );
                lowered.push(c_variable(capture));
            } else {
                // Schema validation admits only stable scalar siblings when a
                // nested call is present. Their value is the same in every
                // C++ argument order, so this evaluation order is faithful.
                lowered.push(self.lower_call_argument(argument)?);
            }
        }
        Ok((evaluation, lowered))
    }

    fn fresh_call_capture(&mut self) -> Result<String, String> {
        let mut capture = format!("{}_{}", self.nested_capture_name, self.next_call_capture);
        self.next_call_capture = self
            .next_call_capture
            .checked_add(1)
            .ok_or("C++ nested call capture counter overflow")?;
        loop {
            crate::instrumentation::record_deterministic_work(1);
            if !self.source_names.contains(capture.as_str()) {
                break;
            }
            capture.push('_');
        }
        Ok(capture)
    }

    fn lower_call_arguments(
        &mut self,
        arguments: &[CppCallArgument],
    ) -> Result<Vec<CExpression>, String> {
        arguments
            .iter()
            .map(|argument| self.lower_call_argument(argument))
            .collect()
    }

    fn lower_cleanup(&self, cleanup: &CppCleanup) -> Result<CStatement, String> {
        let CppCleanup::Destructor { object, callee, .. } = cleanup;
        Ok(c_call(
            callee.name.clone(),
            vec![c_cast(self.lower_place(object)?, CType::Int32Pointer)],
        ))
    }

    fn lower_call_argument(&mut self, argument: &CppCallArgument) -> Result<CExpression, String> {
        match argument {
            CppCallArgument::Value { value } => self.lower_expression(value),
            CppCallArgument::Reference { place } => self.lower_place(place),
            CppCallArgument::Call { .. } => {
                Err("nested C++ call outside a supported return call".into())
            }
        }
    }

    fn lower_expression(&mut self, expression: &CppExpression) -> Result<CExpression, String> {
        match expression {
            CppExpression::IntegerLiteral {
                value, value_type, ..
            }
            | CppExpression::CompilerConstant {
                value, value_type, ..
            } => {
                let error = || format!("unsupported C++ integer constant `{value}`");
                Ok(match cpp_scalar_kernel_type(value_type)? {
                    CType::Int32 => {
                        c_int32_literal(value.parse::<i32>().map_err(|_| error())? as u32)
                    }
                    CType::Int64 => c_int64_literal(value.parse::<i64>().map_err(|_| error())?),
                    CType::UInt32 => c_uint32_literal(value.parse::<u32>().map_err(|_| error())?),
                    CType::UInt64 => c_uint64_literal(value.parse::<u64>().map_err(|_| error())?),
                    _ => return Err(error()),
                })
            }
            CppExpression::ConstantReference { constant, .. } => {
                let resolved = self
                    .constants
                    .get(constant.declaration_id.as_str())
                    .ok_or_else(|| {
                        format!(
                            "C++ lowering found unknown constant declaration `{}`",
                            constant.declaration_id
                        )
                    })?;
                if resolved.name != constant.name {
                    return Err(format!(
                        "C++ constant declaration `{}` changed name during lowering",
                        constant.declaration_id
                    ));
                }
                resolved
                    .evaluated_value
                    .parse::<i64>()
                    .map(c_int64_literal)
                    .map_err(|_| {
                        format!(
                            "C++ constant `{}` has unsupported evaluated value `{}`",
                            resolved.name, resolved.evaluated_value
                        )
                    })
            }
            CppExpression::Load {
                place, value_type, ..
            } => match (&self.place(place)?.value_type, value_type) {
                (
                    CppType::Boolean {
                        bits: 8,
                        is_const: false,
                    },
                    CppType::Boolean {
                        bits: 8,
                        is_const: false,
                    },
                ) => Ok(c_variable(place.name.clone())),
                (CppType::Integer { .. }, CppType::Integer { .. })
                    if cpp_scalar_kernel_type(&self.place(place)?.value_type)?
                        == cpp_scalar_kernel_type(value_type)? =>
                {
                    Ok(c_variable(place.name.clone()))
                }
                (
                    CppType::Pointer { pointee },
                    CppType::Pointer {
                        pointee: value_pointee,
                    },
                ) if is_mutable_int32(pointee) && is_mutable_int32(value_pointee) => {
                    Ok(c_variable(place.name.clone()))
                }
                (CppType::LvalueReference { pointee }, value_type)
                    if (is_mutable_int32(pointee) || is_const_int32(pointee))
                        && is_mutable_int32(value_type) =>
                {
                    let pointer = self.lower_place(place)?;
                    let occurrence = self.next_load_occurrence;
                    self.next_load_occurrence = self
                        .next_load_occurrence
                        .checked_add(1)
                        .ok_or_else(|| "C++ load occurrence capacity exceeded".to_string())?;
                    Ok(c_typed_load_with_source(
                        pointer,
                        CType::Int32,
                        Some(LoadSourceId {
                            owner: LoadSourceOwnerId {
                                source_unit: self.source_unit.into(),
                                function: self.function_name.into(),
                            },
                            occurrence,
                        }),
                    ))
                }
                (CppType::LvalueReference { pointee }, value_type)
                    if is_const_int64(pointee) && is_mutable_int64(value_type) =>
                {
                    let pointer = self.lower_place(place)?;
                    self.lower_typed_load(pointer, CType::Int64)
                }
                _ => Err("C++ load is outside direct bool/reference lowering".into()),
            },
            CppExpression::AddressOf {
                place, value_type, ..
            } => match (&self.place(place)?.value_type, value_type) {
                (CppType::LvalueReference { pointee }, CppType::Pointer { pointee: result })
                    if is_mutable_int32(pointee) && is_mutable_int32(result) =>
                {
                    Ok(c_variable(place.name.clone()))
                }
                _ => Err("C++ address-of is outside mutable `int&` lowering".into()),
            },
            CppExpression::Dereference {
                pointer,
                value_type,
                ..
            } if is_mutable_int32(value_type) && is_mutable_int32_pointer(pointer.value_type()) => {
                self.lower_typed_int32_load(pointer)
            }
            CppExpression::Dereference { .. } => {
                Err("C++ dereference is outside mutable `int*` lowering".into())
            }
            CppExpression::MemberLoad {
                object,
                field,
                value_type,
                ..
            } => {
                let (pointer, field_type) = self.lower_member_pointer(object, field)?;
                if cpp_scalar_kernel_type(value_type)? != field_type {
                    return Err(format!(
                        "C++ member `{}` load type disagrees with its record field",
                        field.name
                    ));
                }
                self.lower_typed_load(pointer, field_type)
            }
            CppExpression::IntegralCast {
                value, value_type, ..
            } => {
                let target = if is_mutable_bool(value_type) {
                    CType::Bool
                } else {
                    cpp_scalar_kernel_type(value_type)?
                };
                let value_expression = self.lower_expression(value)?;
                if matches!(
                    value.value_type(),
                    CppType::Integer {
                        bits: 64,
                        signed: false,
                        ..
                    }
                ) && matches!(
                    value_type,
                    CppType::Integer {
                        bits: 64,
                        signed: true,
                        ..
                    }
                ) {
                    return Ok(crate::kernel::c_uint64_bits_to_int64(value_expression));
                }
                // C++20 signed narrowing is congruent modulo 2^32. The shared
                // unsigned conversion truncates bits; int32 then reinterprets them.
                Ok(
                    if matches!(value.value_type(), CppType::Integer { bits: 64, .. })
                        && is_mutable_int32(value_type)
                    {
                        c_cast(c_cast(value_expression, CType::UInt32), CType::Int32)
                    } else {
                        c_cast(value_expression, target)
                    },
                )
            }
            CppExpression::Binary {
                operator,
                left,
                right,
                value_type,
                ..
            } => {
                let left = self.lower_expression(left)?;
                let right = self.lower_expression(right)?;
                let expression = match operator {
                    CppBinaryOperator::Add => c_add(left, right),
                    CppBinaryOperator::Subtract => c_subtract(left, right),
                    CppBinaryOperator::Multiply => c_multiply(left, right),
                    CppBinaryOperator::Divide => c_divide(left, right),
                    CppBinaryOperator::Remainder => c_remainder(left, right),
                    CppBinaryOperator::Equal => c_equal(left, right),
                    CppBinaryOperator::LessThan => c_less_than(left, right),
                    CppBinaryOperator::GreaterThan => c_greater_than(left, right),
                    CppBinaryOperator::LessEqual => c_less_equal(left, right),
                    CppBinaryOperator::GreaterEqual => c_greater_equal(left, right),
                    CppBinaryOperator::LogicalAnd => c_and(left, right),
                };
                Ok(if is_mutable_bool(value_type) {
                    c_cast(expression, CType::Bool)
                } else {
                    expression
                })
            }
        }
    }

    fn lower_place(&self, place: &CppPlaceReference) -> Result<CExpression, String> {
        self.place(place)?;
        Ok(c_variable(place.name.clone()))
    }

    fn lower_typed_int32_load(&mut self, pointer: &CppExpression) -> Result<CExpression, String> {
        let pointer = self.lower_expression(pointer)?;
        self.lower_typed_load(pointer, CType::Int32)
    }

    fn lower_typed_load(
        &mut self,
        pointer: CExpression,
        value_type: CType,
    ) -> Result<CExpression, String> {
        let occurrence = self.next_load_occurrence;
        self.next_load_occurrence = self
            .next_load_occurrence
            .checked_add(1)
            .ok_or_else(|| "C++ load occurrence capacity exceeded".to_string())?;
        Ok(c_typed_load_with_source(
            pointer,
            value_type,
            Some(LoadSourceId {
                owner: LoadSourceOwnerId {
                    source_unit: self.source_unit.into(),
                    function: self.function_name.into(),
                },
                occurrence,
            }),
        ))
    }

    fn lower_member_pointer(
        &self,
        object: &CppPlaceReference,
        field: &CppFieldReference,
    ) -> Result<(CExpression, CType), String> {
        let place = self.place(object)?;
        let record_type = match &place.value_type {
            CppType::LvalueReference { pointee } => pointee.as_ref(),
            CppType::Record { .. } => &place.value_type,
            _ => {
                return Err(format!(
                    "C++ member object `{}` is not a supported record object",
                    object.name
                ));
            }
        };
        let CppType::Record {
            declaration_id,
            name,
            ..
        } = record_type
        else {
            return Err(format!(
                "C++ member object `{}` is not a supported record object",
                object.name
            ));
        };
        if declaration_id != &field.record_declaration_id {
            return Err(format!(
                "C++ member `{}` does not belong to record `{name}`",
                field.name
            ));
        }
        let record = self.records.get(declaration_id.as_str()).ok_or_else(|| {
            format!("C++ lowering found unknown record declaration `{declaration_id}`")
        })?;
        if record.name != *name {
            return Err(format!(
                "C++ record declaration `{declaration_id}` is named `{}`, not `{name}`",
                record.name
            ));
        }
        let member = record
            .fields
            .iter()
            .find(|candidate| candidate.declaration_id == field.declaration_id)
            .ok_or_else(|| {
                format!(
                    "C++ lowering found unknown field declaration `{}`",
                    field.declaration_id
                )
            })?;
        if member.name != field.name {
            return Err(format!(
                "C++ field declaration `{}` is named `{}`, not `{}`",
                field.declaration_id, member.name, field.name
            ));
        }
        Ok((
            c_pointer_offset_bytes(c_variable(object.name.clone()), member.offset_bytes),
            cpp_scalar_kernel_type(&member.value_type)?,
        ))
    }

    fn place(&self, place: &CppPlaceReference) -> Result<&CppPlace, String> {
        let Some(parameter) = self.places.get(place.declaration_id.as_str()) else {
            return Err(format!(
                "C++ lowering found unknown declaration `{}`",
                place.declaration_id
            ));
        };
        if parameter.name != place.name {
            return Err(format!(
                "C++ declaration `{}` is named `{}`, not `{}`",
                place.declaration_id, parameter.name, place.name
            ));
        }
        Ok(parameter)
    }
}

fn scope_needs_path_sensitive_unwind(statements: &[CppStatement], cleanups: &[CppCleanup]) -> bool {
    let mut may_throw = false;
    for statement in statements {
        if may_throw
            && matches!(
                statement,
                CppStatement::Declare { local, .. }
                    if cleanups.iter().any(|cleanup| match cleanup {
                        CppCleanup::Destructor { object, .. } => {
                            object.declaration_id == local.declaration_id
                                && object.name == local.name
                        }
                    })
            )
        {
            return true;
        }
        may_throw |= statement_may_throw(statement);
    }
    false
}

fn statement_may_throw(statement: &CppStatement) -> bool {
    match statement {
        CppStatement::Call { .. }
        | CppStatement::ReturnCall { .. }
        | CppStatement::Throw { .. } => true,
        CppStatement::Declare {
            initializer: CppInitializer::Call { .. },
            ..
        } => true,
        CppStatement::If {
            then_branch,
            else_branch,
            ..
        } => sequence_may_throw(then_branch) || sequence_may_throw(else_branch),
        CppStatement::TryCatchInt32 {
            try_body, handler, ..
        } => sequence_may_throw(try_body) || sequence_may_throw(handler),
        CppStatement::Scope { body, .. } => sequence_may_throw(body),
        CppStatement::Declare { .. }
        | CppStatement::Assign { .. }
        | CppStatement::Store { .. }
        | CppStatement::MemberStore { .. }
        | CppStatement::Return { .. } => false,
    }
}

fn sequence_may_throw(statements: &[CppStatement]) -> bool {
    statements.iter().any(statement_may_throw)
}

fn return_capture_name(function: &CppFunction) -> String {
    fresh_internal_name(function, "__click_cpp_return_value")
}

fn fresh_internal_name(function: &CppFunction, base: &str) -> String {
    let mut declared_places = Vec::new();
    collect_declared_places(&function.body, &mut declared_places);
    let names = function
        .parameters
        .iter()
        .chain(declared_places)
        .map(|place| place.name.as_str())
        .collect::<std::collections::BTreeSet<_>>();
    if !names.contains(base) {
        return base.to_string();
    }
    for suffix in 1u64.. {
        let candidate = format!("{base}_{suffix}");
        if !names.contains(candidate.as_str()) {
            return candidate;
        }
    }
    unreachable!("an unbounded suffix space contains an unused internal name")
}

fn collect_declared_places<'a>(statements: &'a [CppStatement], places: &mut Vec<&'a CppPlace>) {
    for statement in statements {
        match statement {
            CppStatement::Declare { local, .. } => places.push(local),
            CppStatement::Scope { body, .. } => collect_declared_places(body, places),
            CppStatement::TryCatchInt32 {
                try_body,
                binding,
                handler,
                ..
            } => {
                collect_declared_places(try_body, places);
                places.push(binding);
                collect_declared_places(handler, places);
            }
            CppStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                collect_declared_places(then_branch, places);
                collect_declared_places(else_branch, places);
            }
            _ => {}
        }
    }
}

fn cpp_record_layout(record: &CppRecord) -> Result<CAggregateLayout, String> {
    let fields = record
        .fields
        .iter()
        .map(|field| {
            Ok(CAggregateField::new(
                field.name.clone(),
                field.offset_bytes,
                cpp_scalar_kernel_type(&field.value_type)?,
            ))
        })
        .collect::<Result<Vec<_>, String>>()?;
    Ok(CAggregateLayout::new(
        record.size_bytes,
        record.alignment_bytes,
        fields,
    ))
}

fn cpp_return_scalar_type(value_type: &CppType) -> Result<CType, String> {
    if matches!(
        value_type,
        CppType::Boolean {
            bits: 8,
            is_const: false
        }
    ) {
        Ok(CType::Bool)
    } else {
        cpp_scalar_kernel_type(value_type)
    }
}

fn cpp_scalar_kernel_type(value_type: &CppType) -> Result<CType, String> {
    match value_type {
        CppType::Integer {
            bits: 32,
            signed: true,
            is_const: false,
            ..
        } => Ok(CType::Int32),
        CppType::Integer {
            bits: 64,
            signed: true,
            is_const: false,
            ..
        } => Ok(CType::Int64),
        CppType::Integer {
            bits: 32,
            signed: false,
            is_const: false,
            ..
        } => Ok(CType::UInt32),
        CppType::Integer {
            bits: 64,
            signed: false,
            is_const: false,
            ..
        } => Ok(CType::UInt64),
        _ if is_mutable_int32_pointer(value_type) => Ok(CType::Int32Pointer),
        _ => Err("unsupported C++ scalar kernel type".into()),
    }
}

fn is_mutable_int32(value_type: &CppType) -> bool {
    matches!(
        value_type,
        CppType::Integer {
            bits: 32,
            signed: true,
            is_const: false,
            ..
        }
    )
}

fn is_mutable_bool(value_type: &CppType) -> bool {
    matches!(
        value_type,
        CppType::Boolean {
            bits: 8,
            is_const: false
        }
    )
}

fn is_mutable_int64(value_type: &CppType) -> bool {
    matches!(
        value_type,
        CppType::Integer {
            bits: 64,
            signed: true,
            is_const: false,
            ..
        }
    )
}

fn is_const_int32(value_type: &CppType) -> bool {
    matches!(
        value_type,
        CppType::Integer {
            bits: 32,
            signed: true,
            is_const: true,
            ..
        }
    )
}

fn is_const_int64(value_type: &CppType) -> bool {
    matches!(
        value_type,
        CppType::Integer {
            bits: 64,
            signed: true,
            is_const: true,
            ..
        }
    )
}

fn is_mutable_int32_pointer(value_type: &CppType) -> bool {
    matches!(value_type, CppType::Pointer { pointee } if is_mutable_int32(pointee))
}
