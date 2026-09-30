use super::schema::{Expression as E, Function, Record, RustExport, Statement as S, Type};
mod moves;
use crate::kernel::*;
use crate::languages::c::syntax::{C0Function, C0Parameter, C0StructLayout, C0Type};
use std::collections::{BTreeMap, BTreeSet};

pub(crate) type LoweredRust = (Vec<C0Function>, BTreeMap<String, C0StructLayout>);
fn scalar_type(t: &Type) -> Result<C0Type, String> {
    match t {
        Type::I32 => Ok(C0Type::Int32),
        Type::Bool => Ok(C0Type::Bool),
        Type::Unit => Ok(C0Type::Void),
        Type::Reference { pointee, .. }
            if matches!(pointee.as_ref(), Type::I32 | Type::Record { .. }) =>
        {
            Ok(C0Type::Int32Pointer)
        }
        _ => Err("Rust value type outside direct scalar/reference lowering".into()),
    }
}
pub(crate) fn lower(export: &RustExport) -> Result<LoweredRust, String> {
    let mut layouts = BTreeMap::new();
    let mut fields = BTreeMap::new();
    for record in &export.records {
        let mut layout_fields = record
            .fields
            .iter()
            .map(|f| {
                Ok((
                    f.name.clone(),
                    scalar_type(&f.value_type)?,
                    f.offset,
                    if matches!(f.value_type, Type::Reference { .. }) {
                        8
                    } else {
                        4
                    },
                ))
            })
            .collect::<Result<Vec<_>, String>>()?;
        // Rust may reorder fields; declaration order still selects constructor
        // operands, while layout validation consumes physical offset order.
        layout_fields.sort_by_key(|f| f.2);
        let layout =
            C0StructLayout::from_explicit_fields(layout_fields, record.size, record.alignment)?;
        if layouts.insert(record.name.clone(), layout).is_some() {
            return Err("duplicate Rust record".into());
        }
        for f in &record.fields {
            if fields
                .insert(
                    (record.name.as_str(), f.name.as_str()),
                    (f.offset, scalar_type(&f.value_type)?.to_kernel_type()),
                )
                .is_some()
            {
                return Err("duplicate Rust field".into());
            }
        }
    }
    let record_index = export
        .records
        .iter()
        .map(|r| (r.name.as_str(), r))
        .collect::<BTreeMap<_, _>>();
    let function_index = export
        .functions
        .iter()
        .map(|f| (f.name.as_str(), f))
        .collect::<BTreeMap<_, _>>();
    let mut names = BTreeSet::new();
    let mut functions = Vec::new();
    for f in &export.functions {
        if !names.insert(f.name.clone()) {
            return Err("duplicate Rust function name".into());
        }
        functions.push(lower_function(
            export,
            f,
            &fields,
            &layouts,
            &record_index,
            &function_index,
        )?);
    }
    Ok((functions, layouts))
}
fn lower_function(
    export: &RustExport,
    f: &Function,
    fields: &BTreeMap<(&str, &str), (u32, CType)>,
    layouts: &BTreeMap<String, C0StructLayout>,
    records: &BTreeMap<&str, &Record>,
    functions: &BTreeMap<&str, &Function>,
) -> Result<C0Function, String> {
    if !matches!(f.return_type, Type::I32 | Type::Bool | Type::Unit) {
        return Err("Rust reference/aggregate returns are not supported".into());
    }
    let return_type = scalar_type(&f.return_type)?;
    let mut parameters = Vec::new();
    let mut kernel_parameters = Vec::new();
    let mut locals = BTreeSet::new();
    for p in &f.parameters {
        if !locals.insert(p.name.clone()) {
            return Err("duplicate Rust parameter".into());
        }
        let c_type = scalar_type(&p.value_type)?;
        if c_type == C0Type::Void {
            return Err("unit parameters outside Rust slice".into());
        }
        let (tag, constant) = match &p.value_type {
            Type::Reference { mutable, pointee } => (
                match pointee.as_ref() {
                    Type::Record { name } => Some(name.clone()),
                    _ => None,
                },
                !mutable,
            ),
            _ => (None, false),
        };
        parameters
            .push(C0Parameter::new(c_type, p.name.clone(), tag).with_pointee_constant(constant));
        kernel_parameters
            .push(c_parameter(&p.name, c_type.to_kernel_type()).with_pointee_constant(constant));
    }
    let mut cx = Context {
        owned_locals: BTreeSet::new(),
        source: &export.logical_source,
        function: &f.name,
        fields,
        next_load: 0,
        locals,
        return_type,
        layouts,
        records,
        functions,
    };
    let body = match &f.mir {
        Some(mir) if f.body.is_empty() => moves::lower(&mut cx, f, mir)?,
        Some(_) => return Err("Rust function must select exactly one body representation".into()),
        None => cx.body(&f.body)?,
    };
    let kernel = c_function(
        return_type.to_kernel_type(),
        &f.name,
        kernel_parameters,
        body,
    );
    Ok(
        C0Function::external(return_type, f.name.clone(), parameters)
            .with_prelowered_kernel_function(kernel),
    )
}
struct Context<'a> {
    owned_locals: BTreeSet<String>,
    source: &'a str,
    function: &'a str,
    fields: &'a BTreeMap<(&'a str, &'a str), (u32, CType)>,
    next_load: u32,
    locals: BTreeSet<String>,
    return_type: C0Type,
    layouts: &'a BTreeMap<String, C0StructLayout>,
    records: &'a BTreeMap<&'a str, &'a Record>,
    functions: &'a BTreeMap<&'a str, &'a Function>,
}
impl Context<'_> {
    fn body(&mut self, body: &[S]) -> Result<CStatement, String> {
        let mut result = c_skip();
        for s in body {
            result = c_seq(result, self.statement(s)?);
        }
        Ok(result)
    }
    fn statement(&mut self, s: &S) -> Result<CStatement, String> {
        match s {
            S::Declare { place, initializer } => {
                if !self.locals.insert(place.name.clone()) {
                    return Err("duplicate Rust local identity".into());
                }
                let t = scalar_type(&place.value_type)?;
                if t == C0Type::Void {
                    return Err("unit locals outside Rust slice".into());
                }
                let declaration = c_declare(&place.name, t.to_kernel_type());
                let assign = self.assign(&place.name, initializer)?;
                Ok(c_seq(declaration, assign))
            }
            S::Assign {
                target: E::Local { name },
                value,
            } => self.assign(name, value),
            S::Assign { target, value } => Ok(c_typed_store(
                self.address(target)?,
                self.expr(value)?,
                self.place_type(target)?,
            )),
            S::If {
                condition,
                then_body,
                else_body,
            } => Ok(c_if(
                self.expr(condition)?,
                self.body(then_body)?,
                self.body(else_body)?,
            )),
            S::Return {
                value:
                    Some(E::Call {
                        function,
                        arguments,
                    }),
            } => {
                let mut name = "__rust_return_value".to_string();
                while self.locals.contains(&name) {
                    name.push('_');
                }
                self.locals.insert(name.clone());
                Ok(c_seq(
                    c_declare(&name, self.return_type.to_kernel_type()),
                    c_seq(
                        c_call_assign(&name, function, self.arguments(arguments)?),
                        c_return(c_variable(name)),
                    ),
                ))
            }
            S::Return { value: Some(value) } => Ok(c_return(self.expr(value)?)),
            S::Return { value: None } if self.return_type == C0Type::Void => {
                Ok(c_return(c_void_value()))
            }
            S::Return { value: None } => Err("missing Rust return value".into()),
            S::Call {
                function,
                arguments,
            } => Ok(c_call(function, self.arguments(arguments)?)),
        }
    }
    fn assign(&mut self, name: &str, e: &E) -> Result<CStatement, String> {
        if !self.locals.contains(name) {
            return Err(format!("unknown Rust local `{name}`"));
        }
        match e {
            E::Call {
                function,
                arguments,
            } => Ok(c_call_assign(name, function, self.arguments(arguments)?)),
            _ => Ok(c_assign(name, self.expr(e)?)),
        }
    }
    fn arguments(&mut self, args: &[E]) -> Result<Vec<CExpression>, String> {
        args.iter().map(|e| self.expr(e)).collect()
    }
    fn address(&mut self, e: &E) -> Result<CExpression, String> {
        match e {
            E::Deref { reference } => self.expr(reference),
            E::Field {
                base,
                record,
                field,
            } => {
                let (offset, _) = *self
                    .fields
                    .get(&(record.as_str(), field.as_str()))
                    .ok_or("unknown Rust field")?;
                // Field bases are either record references or local stack objects.
                let pointer = match base.as_ref() {
                    E::Deref { reference } => self.expr(reference)?,
                    _ => self.expr(base)?,
                };
                Ok(c_pointer_offset_bytes(pointer, offset))
            }
            E::Local { name } if self.owned_locals.contains(name) => {
                Ok(c_cast(c_variable(name), CType::Int32Pointer))
            }
            _ => Err("only reference-backed Rust places can be borrowed or stored".into()),
        }
    }
    fn place_type(&self, e: &E) -> Result<CType, String> {
        match e {
            E::Field { record, field, .. } => self
                .fields
                .get(&(record.as_str(), field.as_str()))
                .map(|(_, t)| *t)
                .ok_or("unknown Rust field type".into()),
            E::Deref { .. } => Ok(CType::Int32),
            _ => Err("unsupported Rust memory place type".into()),
        }
    }
    fn expr(&mut self, e: &E) -> Result<CExpression, String> {
        match e {
            E::Integer { value } => Ok(c_int32_literal(*value as u32)),
            E::Boolean { value } => Ok(c_int32_literal(u32::from(*value))),
            E::Local { name } => {
                if !self.locals.contains(name) {
                    return Err(format!("unknown Rust local `{name}`"));
                }
                Ok(c_variable(name))
            }
            E::Not { value } => Ok(c_not(self.expr(value)?)),
            E::Borrow { place } => Ok(c_cast(self.address(place)?, CType::Int32Pointer)),
            E::Deref { .. } | E::Field { .. } => {
                let pointer = self.address(e)?;
                let occurrence = self.next_load;
                self.next_load = self
                    .next_load
                    .checked_add(1)
                    .ok_or("Rust load identity exhausted")?;
                Ok(c_typed_load_with_source(
                    pointer,
                    self.place_type(e)?,
                    Some(LoadSourceId {
                        owner: LoadSourceOwnerId {
                            source_unit: self.source.into(),
                            function: self.function.into(),
                        },
                        occurrence,
                    }),
                ))
            }
            E::Binary {
                operator,
                left,
                right,
            } => {
                let l = self.expr(left)?;
                let r = self.expr(right)?;
                Ok(match operator.as_str() {
                    "add" => c_add(l, r),
                    "sub" => c_subtract(l, r),
                    "mul" => c_multiply(l, r),
                    "eq" => c_equal(l, r),
                    "ne" => c_not_equal(l, r),
                    "lt" => c_less_than(l, r),
                    "le" => c_less_equal(l, r),
                    "gt" => c_greater_than(l, r),
                    "ge" => c_greater_equal(l, r),
                    "and" => c_and(l, r),
                    "or" => c_or(l, r),
                    _ => return Err("unsupported Rust operator in artifact".into()),
                })
            }
            E::Call { .. } => Err("nested Rust calls outside statement lowering".into()),
        }
    }
}
