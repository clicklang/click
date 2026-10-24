//! How specification arithmetic on machine values is read.
//!
//! Arithmetic on machine values takes its meaning from the type its result
//! is used at. Where an Integer is expected, `+`, `-`, `*` and negation are
//! exact Integer operations and each machine operand of them is observed
//! with `to_integer`: an operand of a comparison that reads as Integer, an
//! argument for an `Integer` parameter of a pure function or theorem, the
//! value of `let s: Integer`, an `Integer` constructor field, the body of a
//! `-> Integer` function, and every arm of a `match` in one of those
//! positions. An `if` is not yet one: the kernel has no Integer
//! conditional, so a conditional keeps its C value and is observed whole,
//! `to_integer(if ...)`. Where a machine type is expected the
//! operation is C's at that type, as written. An untyped `let` has no
//! expected type, so one whose value does arithmetic on a machine value is
//! refused and names both annotations.
//!
//! The parser decides this because the reading is a rewrite of the parsed
//! expression (the inserted `to_integer` is what lowering, expansion and
//! diagnostics see), and the expected type of each position above is known
//! from declarations the parser already indexes before it parses bodies.

use super::*;

/// What a name bound inside a specification expression, by a `let` or a
/// `match` arm, is as an arithmetic operand.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum LocalOperand {
    Integer,
    Machine,
    /// A pointer or floating-point value, which has only a C meaning.
    COnly,
    /// A field of a type parameter or a datatype: the parser does not know
    /// its type, so it is never observed.
    Unknown,
}

pub(super) type LocalOperands = BTreeMap<String, LocalOperand>;

/// Binds `bound` in `scope` for the duration of `body`, then restores what
/// each name meant before.
fn with_locals<T>(
    scope: &mut LocalOperands,
    bound: Vec<(String, LocalOperand)>,
    body: impl FnOnce(&mut LocalOperands) -> T,
) -> T {
    let previous = bound
        .into_iter()
        .map(|(name, operand)| {
            let previous = scope.insert(name.clone(), operand);
            (name, previous)
        })
        .collect::<Vec<_>>();
    let result = body(scope);
    for (name, previous) in previous.into_iter().rev() {
        match previous {
            Some(previous) => scope.insert(name, previous),
            None => scope.remove(&name),
        };
    }
    result
}

impl Parser {
    /// A comparison as the file's specification arithmetic reads it. A
    /// comparison that does arithmetic, at the top of an operand or in an
    /// arm of a match there, or that compares an Integer with a machine value,
    /// compares exact Integers: each machine operand of its arithmetic is
    /// observed with `to_integer`, so `x + 1 > x` reads
    /// `to_integer(x) + 1 > to_integer(x)`. A population count is a
    /// quantity, so a comparison with a `count(...)` operand compares
    /// Integers too. A comparison with a pointer operand keeps its C
    /// meaning.
    pub(super) fn reads_as_integer_comparison(
        &self,
        left: &ContractExpression,
        operator: ComparisonOperator,
        right: &ContractExpression,
    ) -> bool {
        if !self.integer_arithmetic || operator == ComparisonOperator::In {
            return false;
        }
        let left_integer = self.integer_operand(left);
        let right_integer = self.integer_operand(right);
        let mixed = left_integer != right_integer;
        let arithmetic = has_arithmetic_spine(left) || has_arithmetic_spine(right);
        let counted = has_count_operand(left) || has_count_operand(right);
        !(left_integer && right_integer)
            && (mixed || arithmetic || counted)
            && !self.has_c_only_operand(left)
            && !self.has_c_only_operand(right)
    }

    pub(super) fn specification_comparison(
        &self,
        left: ContractExpression,
        operator: ComparisonOperator,
        right: ContractExpression,
    ) -> ClickProposition {
        if self.reads_as_integer_comparison(&left, operator, &right) {
            return ClickProposition::Comparison {
                left: self.observe_machine_operands(left),
                operator,
                right: self.observe_machine_operands(right),
            };
        }
        ClickProposition::Comparison {
            left,
            operator,
            right,
        }
    }

    /// `expression` read where an Integer is expected: its arithmetic, if
    /// it does any on values with an Integer observation, is exact.
    pub(super) fn at_integer_position(&self, expression: ContractExpression) -> ContractExpression {
        if self.integer_arithmetic
            && has_arithmetic_spine(&expression)
            && !self.has_c_only_operand(&expression)
        {
            self.observe_machine_operands(expression)
        } else {
            expression
        }
    }

    /// Refuses an untyped `let name = value;` whose value does `+`, `-`, `*`
    /// or negation on a machine value: with no expected type the operation
    /// has no meaning, so the binding must name one.
    pub(super) fn refuse_untyped_machine_arithmetic(
        &self,
        name: &str,
        value: &ContractExpression,
    ) -> Result<(), ClickError> {
        if !self.integer_arithmetic
            || !has_value_arithmetic(value)
            || self.has_c_only_operand(value)
        {
            return Ok(());
        }
        let Some(operand) = self.machine_spine_operand(value, &mut LocalOperands::new()) else {
            return Ok(());
        };
        let machine = self
            .machine_operand_type(operand)
            .map(describe_c0_type)
            .unwrap_or_else(|| "T".to_string());
        Err(self.error(format!(
            "untyped `let {name}` does arithmetic on a machine value; arithmetic takes its \
             meaning from the type its result is used at, so write `let {name}: Integer = ...;` \
             for the exact value or `let {name}: {machine} = ...;` for the C operation"
        )))
    }

    /// Whether `expression` is already an exact Integer: an Integer
    /// binding, a `to_integer` observation, or arithmetic over them.
    pub(super) fn integer_operand(&self, expression: &ContractExpression) -> bool {
        self.integer_operand_in_scope(expression, &mut LocalOperands::new())
    }

    fn integer_operand_in_scope(
        &self,
        expression: &ContractExpression,
        scope: &mut LocalOperands,
    ) -> bool {
        match expression {
            ContractExpression::Add(left, right)
            | ContractExpression::Subtract(left, right)
            | ContractExpression::Multiply(left, right) => {
                self.integer_operand_in_scope(left, scope)
                    || self.integer_operand_in_scope(right, scope)
            }
            ContractExpression::Negate(inner)
            | ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            } => self.integer_operand_in_scope(inner, scope),
            ContractExpression::Let {
                name,
                click_type,
                value,
                body,
            } => {
                let integer = match click_type {
                    Some(ClickType::Integer) => true,
                    Some(_) => false,
                    None => self.integer_operand_in_scope(value, scope),
                };
                let operand = if integer {
                    LocalOperand::Integer
                } else {
                    LocalOperand::Machine
                };
                with_locals(scope, vec![(name.clone(), operand)], |scope| {
                    self.integer_operand_in_scope(body, scope)
                })
            }
            // A match or a conditional is an Integer when a value it can
            // produce is one.
            ContractExpression::If {
                then_branch,
                else_branch,
                ..
            } => {
                self.integer_operand_in_scope(then_branch, scope)
                    || self.integer_operand_in_scope(else_branch, scope)
            }
            ContractExpression::AlgebraicMatch { arms, .. } => arms.iter().any(|arm| {
                with_locals(scope, self.arm_operands(arm), |scope| {
                    self.integer_operand_in_scope(&arm.body, scope)
                })
            }),
            ContractExpression::Binding(name)
            | ContractExpression::CBinding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => match scope.get(name) {
                Some(operand) => *operand == LocalOperand::Integer,
                None => self.integer_leaf(expression),
            },
            leaf => self.integer_leaf(leaf),
        }
    }

    fn integer_leaf(&self, expression: &ContractExpression) -> bool {
        match expression {
            ContractExpression::Call { name, .. } => {
                name == "to_integer"
                    || crate::surface::integer_truncation::is_integer_truncation(name)
                    || self.integer_function_names.contains(name)
            }
            ContractExpression::Binding(name)
            | ContractExpression::CBinding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => {
                self.names.contains_any(NameKind::INTEGERS, name)
                    || matches!(
                        self.names.arm_binding_types.get(name),
                        Some(AlgebraicFieldType::Integer)
                    )
            }
            // A fold is an Integer when a value it can produce is one.
            ContractExpression::RangeFold { initial, body, .. } => {
                self.integer_operand(initial) || self.integer_operand(body)
            }
            _ => false,
        }
    }

    /// What each binding of a `match` arm is as an operand, from its
    /// constructor's declared field types.
    fn arm_operands(&self, arm: &AlgebraicMatchArm) -> Vec<(String, LocalOperand)> {
        let fields = self
            .algebraic_variant_fields
            .get(&(arm.type_name.clone(), arm.variant.clone()))
            .filter(|fields| fields.len() == arm.bindings.len());
        arm.bindings
            .iter()
            .enumerate()
            .map(|(index, binding)| {
                let operand = match fields.map(|fields| &fields[index]) {
                    Some(AlgebraicFieldType::Integer) => LocalOperand::Integer,
                    Some(AlgebraicFieldType::C { c_type, .. })
                        if c_type.is_pointer()
                            || matches!(c_type, C0Type::Float32 | C0Type::Float64) =>
                    {
                        LocalOperand::COnly
                    }
                    Some(AlgebraicFieldType::C { .. }) => LocalOperand::Machine,
                    _ => LocalOperand::Unknown,
                };
                (binding.clone(), operand)
            })
            .collect()
    }

    /// Whether an arithmetic operand of `expression` has only a C meaning:
    /// a pointer parameter, an `address(p)` of a pointer, or a floating-point
    /// value, which has no Integer observation.
    pub(super) fn has_c_only_operand(&self, expression: &ContractExpression) -> bool {
        self.has_c_only_operand_in_scope(expression, &mut LocalOperands::new())
    }

    fn has_c_only_operand_in_scope(
        &self,
        expression: &ContractExpression,
        scope: &mut LocalOperands,
    ) -> bool {
        match expression {
            ContractExpression::Add(left, right)
            | ContractExpression::Subtract(left, right)
            | ContractExpression::Multiply(left, right) => {
                self.has_c_only_operand_in_scope(left, scope)
                    || self.has_c_only_operand_in_scope(right, scope)
            }
            ContractExpression::Negate(inner)
            | ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            } => self.has_c_only_operand_in_scope(inner, scope),
            ContractExpression::AlgebraicMatch { arms, .. } => arms.iter().any(|arm| {
                with_locals(scope, self.arm_operands(arm), |scope| {
                    self.has_c_only_operand_in_scope(&arm.body, scope)
                })
            }),
            ContractExpression::Binding(name)
            | ContractExpression::CBinding(name)
            | ContractExpression::CFragment(CExpression::Variable(name))
                if scope.contains_key(name) =>
            {
                scope[name] == LocalOperand::COnly
            }
            ContractExpression::Binding(name)
            | ContractExpression::CBinding(name)
            | ContractExpression::CFragment(CExpression::Variable(name))
                if matches!(
                    self.names.arm_binding_types.get(name),
                    Some(AlgebraicFieldType::C { c_type, .. }) if c_type.is_pointer()
                ) =>
            {
                true
            }
            // An address, `&r->arr[0]`, or a value cast to a pointer type.
            ContractExpression::CFragment(
                CExpression::AddressOf(_) | CExpression::CheckedObjectAddress(_),
            )
            | ContractExpression::CUnary {
                lowered: CExpression::AddressOf(_) | CExpression::CheckedObjectAddress(_),
                ..
            } => true,
            ContractExpression::CFragment(CExpression::Cast { target_type, .. })
            | ContractExpression::CUnary {
                lowered: CExpression::Cast { target_type, .. },
                ..
            } if target_type.is_pointer() => true,
            ContractExpression::Binding(name)
            | ContractExpression::CBinding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => {
                let c_only = |c_type: &C0Type| {
                    c_type.is_pointer() || matches!(c_type, C0Type::Float32 | C0Type::Float64)
                };
                self.theorem_pointer_params.contains(name)
                    || self.current_local_pointers.contains(name)
                    || self.names.c_parameter_types.get(name).is_some_and(c_only)
                    || (name == "result"
                        && !self.names.c_parameter_types.contains_key(name)
                        && self.current_result_c_type.as_ref().is_some_and(c_only))
            }
            ContractExpression::CFragment(CExpression::TypedLoad { value_type, .. })
            | ContractExpression::CUnary {
                lowered: CExpression::TypedLoad { value_type, .. },
                ..
            }
            | ContractExpression::Field {
                lowered: CExpression::TypedLoad { value_type, .. },
                ..
            } => value_type.is_pointer() || matches!(value_type, CType::Float32 | CType::Float64),
            ContractExpression::CFragment(cast @ CExpression::Cast { .. })
            | ContractExpression::CUnary {
                lowered: cast @ CExpression::Cast { .. },
                ..
            } => self.address_casts.contains(cast),
            _ => false,
        }
    }

    /// `expression` with each machine operand of its arithmetic observed
    /// with `to_integer`, in every arm of a match it produces. Unsuffixed literals take the Integer type from
    /// context, and Integer operands are left as they are.
    pub(super) fn observe_machine_operands(
        &self,
        expression: ContractExpression,
    ) -> ContractExpression {
        self.observe_machine_operands_in_scope(expression, &mut LocalOperands::new())
    }

    fn observe_machine_operands_in_scope(
        &self,
        expression: ContractExpression,
        scope: &mut LocalOperands,
    ) -> ContractExpression {
        let observe = |expression: Box<ContractExpression>, scope: &mut LocalOperands| {
            Box::new(self.observe_machine_operands_in_scope(*expression, scope))
        };
        match expression {
            ContractExpression::Add(left, right) => {
                ContractExpression::Add(observe(left, scope), observe(right, scope))
            }
            ContractExpression::Subtract(left, right) => {
                ContractExpression::Subtract(observe(left, scope), observe(right, scope))
            }
            ContractExpression::Multiply(left, right) => {
                ContractExpression::Multiply(observe(left, scope), observe(right, scope))
            }
            ContractExpression::Negate(inner) => ContractExpression::Negate(observe(inner, scope)),
            ContractExpression::Old(inner) if has_arithmetic_spine(&inner) => {
                ContractExpression::Old(observe(inner, scope))
            }
            ContractExpression::At {
                selector,
                expression,
            } if has_arithmetic_spine(&expression)
                || self.integer_operand_in_scope(&expression, scope) =>
            {
                ContractExpression::At {
                    selector,
                    expression: observe(expression, scope),
                }
            }
            // Each arm is in the position the match is in.
            ContractExpression::AlgebraicMatch { scrutinee, arms } => {
                ContractExpression::AlgebraicMatch {
                    scrutinee,
                    arms: arms
                        .into_iter()
                        .map(|arm| {
                            let bound = self.arm_operands(&arm);
                            let AlgebraicMatchArm {
                                type_name,
                                variant,
                                bindings,
                                body,
                            } = arm;
                            let body = with_locals(scope, bound, |scope| {
                                self.observe_machine_operands_in_scope(body, scope)
                            });
                            AlgebraicMatchArm {
                                type_name,
                                variant,
                                bindings,
                                body,
                            }
                        })
                        .collect(),
                }
            }
            ContractExpression::IntegerLiteral(value) => ContractExpression::IntegerLiteral(value),
            ContractExpression::Binding(ref name)
            | ContractExpression::CBinding(ref name)
            | ContractExpression::CFragment(CExpression::Variable(ref name))
                if scope.get(name) == Some(&LocalOperand::Unknown) =>
            {
                expression
            }
            // An Integer operand, including one under `old` or `at`, is
            // already exact.
            leaf if self.integer_operand_in_scope(&leaf, scope) => leaf,
            leaf => ContractExpression::Call {
                name: "to_integer".to_string(),
                arguments: vec![leaf],
            },
        }
    }

    /// The first operand of `expression`'s arithmetic, through its
    /// branches, that is a machine value.
    fn machine_spine_operand<'a>(
        &self,
        expression: &'a ContractExpression,
        scope: &mut LocalOperands,
    ) -> Option<&'a ContractExpression> {
        match expression {
            ContractExpression::Add(left, right)
            | ContractExpression::Subtract(left, right)
            | ContractExpression::Multiply(left, right) => self
                .machine_spine_operand(left, scope)
                .or_else(|| self.machine_spine_operand(right, scope)),
            ContractExpression::Negate(inner) => self.machine_spine_operand(inner, scope),
            ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            } if has_value_arithmetic(inner) => self.machine_spine_operand(inner, scope),
            ContractExpression::If {
                then_branch,
                else_branch,
                ..
            } => self
                .machine_spine_operand(then_branch, scope)
                .or_else(|| self.machine_spine_operand(else_branch, scope)),
            ContractExpression::AlgebraicMatch { arms, .. } => arms.iter().find_map(|arm| {
                with_locals(scope, self.arm_operands(arm), |scope| {
                    self.machine_spine_operand(&arm.body, scope)
                })
            }),
            ContractExpression::IntegerLiteral(_) => None,
            ContractExpression::Binding(name)
            | ContractExpression::CBinding(name)
            | ContractExpression::CFragment(CExpression::Variable(name))
                if scope.contains_key(name) =>
            {
                (scope[name] == LocalOperand::Machine).then_some(expression)
            }
            leaf if self.integer_operand_in_scope(leaf, scope)
                || self.has_c_only_operand_in_scope(leaf, scope) =>
            {
                None
            }
            leaf => Some(leaf),
        }
    }

    /// The machine type of an arithmetic operand, where its spelling shows
    /// it: a parameter, `result`, a suffixed constant, a load or a cast.
    fn machine_operand_type(&self, operand: &ContractExpression) -> Option<C0Type> {
        match operand {
            ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            } => self.machine_operand_type(inner),
            ContractExpression::Binding(name)
            | ContractExpression::CBinding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => self
                .names
                .c_parameter_types
                .get(name)
                .or_else(|| self.spec_parameter_types.get(name))
                .copied()
                .or_else(|| {
                    (name == "result")
                        .then_some(self.current_result_c_type)
                        .flatten()
                }),
            ContractExpression::CFragment(lowered) | ContractExpression::CUnary { lowered, .. } => {
                match lowered {
                    CExpression::Value(value) => Some(
                        crate::surface::generics::c0_type_from_kernel(value.c_type()),
                    ),
                    CExpression::TypedLoad { value_type, .. }
                    | CExpression::Cast {
                        target_type: value_type,
                        ..
                    } => Some(crate::surface::generics::c0_type_from_kernel(*value_type)),
                    _ => None,
                }
            }
            ContractExpression::Field {
                lowered: CExpression::TypedLoad { value_type, .. },
                ..
            } => Some(crate::surface::generics::c0_type_from_kernel(*value_type)),
            _ => None,
        }
    }
}

/// Whether `expression` or an operand of its arithmetic is a population
/// count, looking through `old`.
pub(super) fn has_count_operand(expression: &ContractExpression) -> bool {
    match expression {
        ContractExpression::ResourceCount(_) => true,
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right) => {
            has_count_operand(left) || has_count_operand(right)
        }
        ContractExpression::Negate(inner) | ContractExpression::Old(inner) => {
            has_count_operand(inner)
        }
        _ => false,
    }
}

/// Whether the value of `expression` is computed by `+`, `-`, `*` or
/// negation: at its top, through `old` and `at`, or in a branch of a
/// conditional or an arm of a match.
fn has_value_arithmetic(expression: &ContractExpression) -> bool {
    match expression {
        ContractExpression::Old(inner)
        | ContractExpression::At {
            expression: inner, ..
        } => has_value_arithmetic(inner),
        ContractExpression::If {
            then_branch,
            else_branch,
            ..
        } => has_value_arithmetic(then_branch) || has_value_arithmetic(else_branch),
        ContractExpression::AlgebraicMatch { arms, .. } => {
            arms.iter().any(|arm| has_value_arithmetic(&arm.body))
        }
        _ => has_arithmetic_spine(expression),
    }
}

/// Whether `expression` does `+`, `-`, `*` or negation at its top, looking
/// through `old`, `at`, and the arms of a match, each of which is in the
/// position the whole is in. A conditional is not looked through: the
/// kernel has no Integer conditional, so an `if` keeps its C value.
pub(super) fn has_arithmetic_spine(expression: &ContractExpression) -> bool {
    match expression {
        ContractExpression::Add(..)
        | ContractExpression::Subtract(..)
        | ContractExpression::Multiply(..) => true,
        // A negative literal, `-128`, is a constant, not arithmetic.
        ContractExpression::Negate(inner) => {
            !matches!(inner.as_ref(), ContractExpression::IntegerLiteral(_))
        }
        ContractExpression::Old(inner)
        | ContractExpression::At {
            expression: inner, ..
        } => has_arithmetic_spine(inner),
        ContractExpression::AlgebraicMatch { arms, .. } => {
            arms.iter().any(|arm| has_arithmetic_spine(&arm.body))
        }
        _ => false,
    }
}

/// The positions of a declaration's written `name: Integer` parameters,
/// for the parameter list that opens at or after `start`, when it has any.
/// Reads tokens only.
pub(in crate::surface) fn written_integer_parameters(
    tokens: &[Token],
    start: usize,
) -> Option<Vec<usize>> {
    let open = start
        + tokens
            .get(start..)?
            .iter()
            .position(|token| *token == Token::LParen)?;
    let mut depth = 0usize;
    let mut index_in_list = 0usize;
    let mut parameter_start = Some(open + 1);
    let mut integers = Vec::new();
    for index in open + 1..tokens.len() {
        let token = &tokens[index];
        if parameter_start == Some(index) && *token != Token::RParen {
            if matches!(token, Token::Ident(_))
                && tokens.get(index + 1) == Some(&Token::Colon)
                && matches!(tokens.get(index + 2), Some(Token::Ident(name)) if name == "Integer")
                && matches!(tokens.get(index + 3), Some(Token::Comma | Token::RParen))
            {
                integers.push(index_in_list);
            }
            index_in_list += 1;
        }
        match token {
            Token::LParen | Token::LBracket | Token::LessThan => depth += 1,
            Token::RParen if depth == 0 => break,
            Token::RParen | Token::RBracket | Token::GreaterThan => depth = depth.saturating_sub(1),
            // `List<Box<T>>` closes two argument lists.
            Token::ShiftRight => depth = depth.saturating_sub(2),
            Token::Comma if depth == 0 => parameter_start = Some(index + 1),
            _ => {}
        }
    }
    (!integers.is_empty()).then_some(integers)
}

impl Parser {
    /// The positions of the `Integer` parameters of the pure function or
    /// theorem `name`: one this module declares or imports, a library one,
    /// or a built-in Integer function.
    fn integer_parameters_of(&self, name: &str) -> Option<&[usize]> {
        if crate::surface::integer_truncation::is_integer_truncation(name) {
            return Some(&[0, 1]);
        }
        self.integer_parameter_positions
            .get(name)
            .or_else(|| names::library_integer_parameters().get(name))
            .map(Vec::as_slice)
    }

    /// The written arguments of a call to `name`, each one passed for an
    /// `Integer` parameter read at an Integer position.
    pub(super) fn observe_integer_arguments(
        &self,
        name: &str,
        mut arguments: Vec<ContractExpression>,
    ) -> Vec<ContractExpression> {
        let Some(positions) = self.integer_parameters_of(name) else {
            return arguments;
        };
        for &position in positions {
            if let Some(argument) = arguments.get_mut(position) {
                let written = std::mem::replace(argument, ContractExpression::ResourceWildcard);
                *argument = self.at_integer_position(written);
            }
        }
        arguments
    }

    /// The arguments of a datatype constructor, each one for an `Integer`
    /// field read at an Integer position.
    pub(super) fn observe_integer_fields(
        &self,
        type_name: &str,
        variant: &str,
        mut arguments: Vec<ContractExpression>,
    ) -> Vec<ContractExpression> {
        let Some(fields) = self
            .algebraic_variant_fields
            .get(&(type_name.to_string(), variant.to_string()))
        else {
            return arguments;
        };
        for (argument, field) in arguments.iter_mut().zip(fields) {
            if *field == AlgebraicFieldType::Integer {
                let written = std::mem::replace(argument, ContractExpression::ResourceWildcard);
                *argument = self.at_integer_position(written);
            }
        }
        arguments
    }
}
