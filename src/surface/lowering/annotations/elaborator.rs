//! Elaboration's type queries, apart from the lowerer
//! (`design/typed-surface.md`). An `Elaborator` reads the declarations, the
//! specification definitions, the recorded states and a typing environment,
//! and nothing that lowering builds, so elaboration can be run without
//! lowering. The lowerer builds one for each query and delegates to it.
use super::*;

#[derive(Clone)]
pub(super) struct Elaborator<'a> {
    pub(super) declarations: Declarations<'a>,
    pub(super) definitions: SpecDefinitions<'a>,
    pub(super) retained_states: Option<&'a RecordedStates>,
}

impl<'a> AnnotationLowerer<'a> {
    /// The lowerer's elaboration queries, as a value independent of it.
    pub(super) fn elaborator(&self) -> Elaborator<'a> {
        Elaborator {
            declarations: self.declarations(),
            definitions: self.spec_definitions,
            retained_states: self.retained_states,
        }
    }
}

impl Elaborator<'_> {
    fn program_name_type(
        &self,
        name: impl Into<crate::kernel::BindingName>,
        typing: &TypingEnvironment<'_>,
    ) -> Option<ProgramType> {
        self.declarations.program_name_type(name, typing)
    }

    fn program_expression_array_element_type(
        &self,
        expression: &ProgramExpression,
        typing: &TypingEnvironment<'_>,
    ) -> Option<ProgramType> {
        self.declarations
            .program_expression_array_element_type(expression, typing)
    }

    pub(super) fn contract_expression_is_integer(
        &self,
        expression: &SyntaxTerm,
        typing: &TypingEnvironment<'_>,
    ) -> bool {
        let mut depth = 0;
        let mut current = expression;
        while let SyntaxTerm::Add(left, right) = current {
            if !matches!(right.as_ref(), SyntaxTerm::IntegerLiteral(_)) {
                break;
            }
            depth += 1;
            current = left;
        }
        if depth > 128 && matches!(current, SyntaxTerm::IntegerLiteral(_)) {
            return false;
        }
        self.contract_expression_click_type(expression, typing)
            .is_some_and(|click_type| click_type == ClickType::Integer)
    }

    /// Infer the result kind needed when choosing between the C and Integer
    /// lowering paths.  Surface validation already checks algebraic match
    /// arms against their datatype schema, but the fixed-state lowerer does
    /// not retain that result type in the syntax tree.  Recover it here so a
    /// match whose arms return an Integer binding is still recognized when
    /// the other comparison operand is an untyped numeral.
    pub(super) fn contract_expression_click_type(
        &self,
        expression: &SyntaxTerm,
        typing: &TypingEnvironment<'_>,
    ) -> Option<ClickType> {
        self.contract_expression_click_type_in_scope(expression, typing, &mut Vec::new())
    }

    pub(super) fn contract_expression_click_type_in_scope(
        &self,
        expression: &SyntaxTerm,
        typing: &TypingEnvironment<'_>,
        lexical_bindings: &mut Vec<(SurfaceBinder, Option<ClickType>)>,
    ) -> Option<ClickType> {
        if let Some(id) = expression.generated_binder() {
            if let Some((_, ty)) = lexical_bindings
                .iter()
                .rev()
                .find(|(name, _)| name == &SurfaceBinder::Generated(id))
            {
                return ty.clone();
            }
            return typing.binding_click_type(&id);
        }

        match expression {
            SyntaxTerm::IntegerContext(_) => Some(ClickType::Integer),

            SyntaxTerm::Lambda {
                parameters, result, ..
            } => Some(lambdas::signature(parameters, result)),
            SyntaxTerm::Apply { function, .. } => match self
                .contract_expression_click_type_in_scope(function, typing, lexical_bindings)?
            {
                ClickType::Function { result, .. } => Some(*result),
                _ => None,
            },

            SyntaxTerm::ResourceField(access) => access.click_type.clone(),
            SyntaxTerm::IntegerLiteral(_) => None,
            SyntaxTerm::Binding(name) => {
                if let Some((_, click_type)) = lexical_bindings
                    .iter()
                    .rev()
                    .find(|(binding, _)| binding == name)
                {
                    click_type.clone()
                } else {
                    typing.binding_click_type(name)
                }
            }
            SyntaxTerm::AlgebraicVariable { algebraic_type, .. }
            | SyntaxTerm::AlgebraicConstructor { algebraic_type, .. } => {
                Some(ClickType::Algebraic(algebraic_type.clone()))
            }
            SyntaxTerm::Negate(inner)
            | SyntaxTerm::Old(inner)
            | SyntaxTerm::Exact(inner)
            | SyntaxTerm::At {
                expression: inner, ..
            } => self.contract_expression_click_type_in_scope(inner, typing, lexical_bindings),
            SyntaxTerm::Add(left, right)
            | SyntaxTerm::Subtract(left, right)
            | SyntaxTerm::Multiply(left, right) => {
                let left =
                    self.contract_expression_click_type_in_scope(left, typing, lexical_bindings);
                let right =
                    self.contract_expression_click_type_in_scope(right, typing, lexical_bindings);
                if left == Some(ClickType::Integer) || right == Some(ClickType::Integer) {
                    Some(ClickType::Integer)
                } else {
                    left.or(right)
                }
            }
            SyntaxTerm::RangeFold {
                start,
                end,
                initial,
                accumulator,
                item,
                body,
                ..
            } => {
                // The index carrier and accumulator carrier are independent.
                // In particular, an Int32 index can feed a C array load while
                // `to_integer(...)` makes the accumulator mathematical.  A
                // fold's result follows the accumulator/body type; the
                // endpoint type only selects the item carrier in the body.
                let start_type =
                    self.contract_expression_click_type_in_scope(start, typing, lexical_bindings);
                let end_type =
                    self.contract_expression_click_type_in_scope(end, typing, lexical_bindings);
                let integer_index =
                    start_type == Some(ClickType::Integer) || end_type == Some(ClickType::Integer);
                let initial_type =
                    self.contract_expression_click_type_in_scope(initial, typing, lexical_bindings);
                let lexical_len = lexical_bindings.len();
                let accumulator_type = initial_type.clone();
                lexical_bindings.push((accumulator.clone(), accumulator_type));
                lexical_bindings.push((
                    item.clone(),
                    if integer_index {
                        Some(ClickType::Integer)
                    } else {
                        Some(ClickType::Program(InterfaceType::Int32))
                    },
                ));
                let body_type =
                    self.contract_expression_click_type_in_scope(body, typing, lexical_bindings);
                lexical_bindings.truncate(lexical_len);
                if initial_type == Some(ClickType::Integer) || body_type == Some(ClickType::Integer)
                {
                    Some(ClickType::Integer)
                } else {
                    initial_type.or(body_type)
                }
            }
            SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => {
                if let Some((_, click_type)) = lexical_bindings
                    .iter()
                    .rev()
                    .find(|(binding, _)| binding == name)
                {
                    click_type.clone()
                } else {
                    typing.binding_click_type(name)
                }
            }
            SyntaxTerm::ProgramBinding(name) => lexical_bindings
                .iter()
                .rev()
                .find_map(|(binding, click_type)| (binding == name).then(|| click_type.clone()))
                .flatten()
                .or_else(|| typing.program_binding_click_type(name)),
            SyntaxTerm::Let {
                name,
                click_type: Some(ClickType::Integer),
                value: _,
                body,
            } => {
                lexical_bindings.push((name.clone(), Some(ClickType::Integer)));
                let body_type =
                    self.contract_expression_click_type_in_scope(body, typing, lexical_bindings);
                lexical_bindings.pop();
                body_type
            }
            SyntaxTerm::Let {
                name,
                click_type: _,
                value,
                body,
            } => {
                let value_type =
                    self.contract_expression_click_type_in_scope(value, typing, lexical_bindings);
                lexical_bindings.push((name.clone(), value_type));
                let body_type =
                    self.contract_expression_click_type_in_scope(body, typing, lexical_bindings);
                lexical_bindings.pop();
                body_type
            }
            SyntaxTerm::AlgebraicMatch { scrutinee, arms } => {
                let Some(ClickType::Algebraic(application)) = self
                    .contract_expression_click_type_in_scope(scrutinee, typing, lexical_bindings)
                else {
                    return None;
                };
                let Ok(algebraic_type) =
                    algebraic_kernel_type(self.definitions.functions, &application)
                else {
                    return None;
                };
                let variants = algebraic_type
                    .variants
                    .iter()
                    .map(|variant| (variant.name.as_str(), variant))
                    .collect::<BTreeMap<_, _>>();
                crate::instrumentation::record_deterministic_work(algebraic_type.variants.len());
                let mut result_type = None;
                let mut has_contextual_literal = false;
                for arm in arms {
                    crate::instrumentation::record_deterministic_work(1);
                    let variant = variants.get(arm.variant.as_str())?;
                    if arm.bindings.len() != variant.fields.len() {
                        return None;
                    }
                    let lexical_len = lexical_bindings.len();
                    for (binding, field) in arm.bindings.iter().zip(&variant.fields) {
                        lexical_bindings.push((
                            binding.clone(),
                            Some(generics::click_type_from_algebraic_value_type(field)),
                        ));
                    }
                    let arm_type = self.contract_expression_click_type_in_scope(
                        &arm.body,
                        typing,
                        lexical_bindings,
                    );
                    lexical_bindings.truncate(lexical_len);
                    let Some(arm_type) = arm_type else {
                        if is_unsuffixed_integer_literal_expression(&arm.body) {
                            // A numeral arm stays untyped until another arm
                            // supplies the match result carrier.  In
                            // particular, do not make an all-literal match
                            // mathematical Integer by default.
                            has_contextual_literal = true;
                            continue;
                        }
                        return None;
                    };
                    if let Some(previous) = &result_type
                        && previous != &arm_type
                    {
                        return None;
                    }
                    result_type = Some(arm_type);
                }
                if has_contextual_literal
                    && !matches!(
                        result_type.as_ref(),
                        Some(ClickType::Integer) | Some(ClickType::Program(_))
                    )
                {
                    return None;
                }
                result_type
            }
            // An Integer conditional: Integer branches, or one Integer branch
            // and an unsuffixed numeral, which takes its type. Any other
            // conditional keeps its C lowering, so it is not typed here.
            SyntaxTerm::If {
                then_branch,
                else_branch,
                ..
            } => {
                let then_type = self.contract_expression_click_type_in_scope(
                    then_branch,
                    typing,
                    lexical_bindings,
                );
                let else_type = self.contract_expression_click_type_in_scope(
                    else_branch,
                    typing,
                    lexical_bindings,
                );
                let integer_or_numeral = |branch_type: &Option<ClickType>, branch| {
                    *branch_type == Some(ClickType::Integer)
                        || (branch_type.is_none()
                            && is_unsuffixed_integer_literal_expression(branch))
                };
                ((then_type == Some(ClickType::Integer) || else_type == Some(ClickType::Integer))
                    && integer_or_numeral(&then_type, then_branch)
                    && integer_or_numeral(&else_type, else_branch))
                .then_some(ClickType::Integer)
            }
            SyntaxTerm::Call { name, .. }
                if name == "to_integer" || is_integer_truncation(name) =>
            {
                Some(ClickType::Integer)
            }
            SyntaxTerm::Call { name, .. } => self
                .definitions
                .functions
                .get(name)
                .map(|function| function.return_type().clone()),
            _ => None,
        }
    }

    /// The Rust enum type of C name `name`, a parameter, local or `result`
    /// that holds an enum's value.
    pub(super) fn enum_program_name_type(
        &self,
        name: &str,
        typing: &TypingEnvironment<'_>,
    ) -> Option<crate::kernel::TypeParameterName> {
        match self.program_name_type(name, typing)? {
            ProgramType::Parameter(enum_type) if crate::surface::holds_spec_value(enum_type) => {
                Some(enum_type)
            }
            _ => None,
        }
    }

    /// The enum or library value type named by a program binding or read.
    pub(super) fn enum_program_value_type(
        &self,
        expression: &SyntaxTerm,
        typing: &TypingEnvironment<'_>,
    ) -> Option<crate::kernel::TypeParameterName> {
        match expression {
            SyntaxTerm::Binding(name)
            | SyntaxTerm::ProgramBinding(name)
            | SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => self.enum_program_name_type(name, typing),
            SyntaxTerm::ProgramExpression(ProgramExpression::Load(pointer)) => {
                let value_type = match pointer.as_ref() {
                    ProgramExpression::Variable(name) => {
                        self.program_name_type(name, typing)?.pointee_type()?
                    }
                    _ => self.program_expression_array_element_type(pointer, typing)?,
                };
                match value_type {
                    ProgramType::Parameter(ty) if crate::surface::holds_spec_value(ty) => Some(ty),
                    _ => None,
                }
            }
            SyntaxTerm::MemoryLoad {
                value_type: ProgramType::Parameter(ty),
                ..
            } if crate::surface::holds_spec_value(*ty) => Some(*ty),
            SyntaxTerm::Old(inner) => self.enum_program_value_type(inner, typing),
            // The enum value a call returned.
            SyntaxTerm::RegionResult(region) => {
                match self
                    .retained_states?
                    .region_result_value_at(region, typing.call_result_point())
                    .ok()?
                {
                    ProgramValue::Parameter(term) => {
                        let enum_type = crate::kernel::TypeParameterName::of(&term.algebraic_type);
                        crate::surface::holds_spec_value(enum_type).then_some(enum_type)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    pub(super) fn contract_pointer_element_type(
        &self,
        expression: &SyntaxTerm,
        typing: &TypingEnvironment<'_>,
    ) -> Option<ProgramType> {
        match expression {
            SyntaxTerm::MemoryLoad { value_type, .. } => value_type.pointee_type(),
            SyntaxTerm::ResourceField(access) => access
                .click_type
                .as_ref()?
                .interface_type()?
                .pointee_type()
                .map(InterfaceType::to_kernel_type),
            SyntaxTerm::CUnary { operand, lowered } => match lowered {
                ProgramExpression::Cast { target_type, .. } => target_type.pointee_type(),
                ProgramExpression::PointerOffsetBytes { .. } => {
                    self.contract_pointer_element_type(operand, typing)
                }
                _ => self.program_expression_array_element_type(lowered, typing),
            },
            SyntaxTerm::ProgramBinding(name) => typing
                .bound_array_element_type(name)
                .or_else(|| typing.bound_pointer_pointee_type(name)),
            SyntaxTerm::QualifiedC {
                lowered: expression,
                ..
            }
            | SyntaxTerm::ProgramExpression(expression)
            | SyntaxTerm::Field {
                lowered: expression,
                ..
            } => self.program_expression_array_element_type(expression, typing),
            SyntaxTerm::Old(expression)
            | SyntaxTerm::Exact(expression)
            | SyntaxTerm::At { expression, .. } => {
                self.contract_pointer_element_type(expression, typing)
            }
            SyntaxTerm::Add(left, right) => self
                .contract_pointer_element_type(left, typing)
                .or_else(|| self.contract_pointer_element_type(right, typing)),
            SyntaxTerm::Subtract(left, _) => self.contract_pointer_element_type(left, typing),
            _ => None,
        }
    }
}
