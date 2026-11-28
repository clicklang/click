//! The `defined(...)` special form: the domain of an expression's root
//! operation, with its operands taken as values.
//!
//! Each operand is evaluated once, as an ordinary term. Its obligations stay
//! obligations of the lowered proposition, exactly as `ensures r == a + b`
//! owes `a + b`'s domain without claiming it. Its value is bound to a fresh
//! generated name, and the root is evaluated over those names, from no facts
//! and with C's evaluation rules. What that evaluation owes or selects is the
//! claim. A bound name reads its value and owes nothing, so the claim is the
//! root operation's own domain, the same kernel conditions the whole
//! expression's evaluation owes for that operation.
//!
//! `let` and loop entry are transparent, and a `let` whose body is its own
//! name is its value's operation. A conversion to its operand's own
//! type is transparent; any other conversion is the operation. `if` claims
//! its selected branch's domain under its condition, as `and`, `or` and
//! `implies` read their right sides. A form with no operand expressions is
//! evaluated whole.

use super::*;

struct DefinedPath {
    claim: Proposition,
    /// The value the root evaluation produced, when it produced one value.
    value: Option<SpecValue>,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
}

// Keep this lowering's paths and operand states out of the recursive
// proposition lowerer's frame.
#[inline(never)]
pub(super) fn lower(
    scope: SpecScope<'_>,
    expression: &SpecExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<SpecPropositionPath>> {
    Ok(paths(scope, expression, assumptions, budget)?
        .into_iter()
        .map(|path| SpecPropositionPath {
            introductions: Vec::new(),
            proposition: path.claim,
            facts: path.facts,
            obligations: path.obligations,
        })
        .collect())
}

fn paths(
    scope: SpecScope<'_>,
    expression: &SpecExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<DefinedPath>> {
    crate::instrumentation::record_deterministic_work(1);
    match expression {
        SpecExpression::Cast(operand, target)
        | SpecExpression::PointerCoercion(operand, target) => {
            conversion(scope, expression, operand, *target, assumptions, budget)
        }
        SpecExpression::LoopEntryState(inner) => {
            let Some(entry) = scope.loop_entry_state else {
                return Ok(Vec::new());
            };
            paths(
                SpecScope {
                    state: entry,
                    loop_entry_state: Some(entry),
                    values: None,
                    ..scope
                },
                inner,
                assumptions,
                budget,
            )
        }
        // A `let` whose body is its own name, possibly under conversions, as
        // a Click function or lambda application binds its result, is those
        // conversions of its value: its value's operation is the root.
        SpecExpression::Let { name, value, body }
            if let Some(result) = substitute_bound_result(name, value, body) =>
        {
            paths(scope, &result, assumptions, budget)
        }
        SpecExpression::Let { name, value, body } => {
            let mut result = Vec::new();
            for value_path in evaluate_spec_expression_paths_with_algebraic_bindings_in(
                scope,
                value,
                assumptions,
                budget,
            )? {
                let mut state = scope.state.clone();
                let mut values = scope.values.cloned().unwrap_or_default();
                bindings::bind_value(name, value_path.value, &mut state, &mut values);
                let context = assumptions_with_path_context(
                    assumptions,
                    &value_path.facts,
                    &value_path.obligations,
                );
                let body_scope = SpecScope {
                    state: &state,
                    values: Some(&values),
                    ..scope
                };
                for body_path in paths(body_scope, body, &context, budget)? {
                    let Some((facts, obligations)) =
                        merge_execution_pure_facts_and_obligations_under(
                            &value_path.facts,
                            &value_path.obligations,
                            &body_path.facts,
                            &body_path.obligations,
                            assumptions,
                            &context,
                        )
                    else {
                        continue;
                    };
                    result.push(DefinedPath {
                        facts,
                        obligations,
                        ..body_path
                    });
                }
            }
            Ok(result)
        }
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => conditional(
            scope,
            condition,
            then_branch,
            else_branch,
            assumptions,
            budget,
        ),
        SpecExpression::AlgebraicMatch { scrutinee, arms } => {
            algebraic_match(scope, scrutinee, arms, assumptions, budget)
        }
        SpecExpression::ProgramExpression(fragment)
            if let Some((condition, then_branch, else_branch)) = fragment_conditional(fragment) =>
        {
            conditional(
                scope,
                &condition,
                &then_branch,
                &else_branch,
                assumptions,
                budget,
            )
        }
        _ => operation(scope, expression, assumptions, budget),
    }
}

/// A `match` claims its taken arm's root: the scrutinee is an operand,
/// evaluated once as an ordinary term, and each arm's body claims its own
/// root where its pattern matches, as `if` claims its taken branch's. The
/// claim is the match of `1` where the arm's claim holds and `0` elsewhere,
/// compared with `1`, so the kernel's match guards each arm's obligations by
/// its pattern.
fn algebraic_match(
    scope: SpecScope<'_>,
    scrutinee: &SpecAlgebraicExpression,
    arms: &[SpecAlgebraicMatchArm],
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<DefinedPath>> {
    use crate::kernel::program_expression::int32_literal;
    let claim_arms = arms
        .iter()
        .map(|arm| SpecAlgebraicMatchArm {
            body: SpecExpression::If {
                condition: Box::new(SpecProposition::OperationDefined(arm.body.clone())),
                then_branch: Box::new(SpecExpression::ProgramExpression(int32_literal(1))),
                else_branch: Box::new(SpecExpression::ProgramExpression(int32_literal(0))),
            },
            ..arm.clone()
        })
        .collect::<Vec<_>>();
    let mut result = Vec::new();
    for scrutinee_path in
        evaluate_spec_algebraic_at_state_with_bindings_in(scope, scrutinee, assumptions, budget)?
    {
        let name = crate::kernel::GeneratedBinderId::fresh().binding_name();
        let mut algebraic = scope.algebraic_bindings.clone();
        algebraic.insert(name.clone(), scrutinee_path.value.into_native_compat());
        let claim = SpecProposition::Comparison {
            left: SpecExpression::AlgebraicMatch {
                scrutinee: Box::new(SpecAlgebraicExpression {
                    algebraic_type: scrutinee.algebraic_type.clone(),
                    node: SpecAlgebraicExpressionNode::Binding(name),
                }),
                arms: claim_arms.clone(),
            },
            operator: ComparisonOperator::Equal,
            right: SpecExpression::ProgramExpression(int32_literal(1)),
        };
        let context = assumptions_with_path_context(
            assumptions,
            &scrutinee_path.facts,
            &scrutinee_path.obligations,
        );
        for claim_path in lower_spec_proposition_at_state_with_algebraic_bindings_in(
            SpecScope {
                algebraic_bindings: &algebraic,
                ..scope
            },
            &claim,
            &context,
            budget,
        )? {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations_under(
                &scrutinee_path.facts,
                &scrutinee_path.obligations,
                &claim_path.facts,
                &claim_path.obligations,
                assumptions,
                &context,
            ) else {
                continue;
            };
            result.push(DefinedPath {
                claim: claim_path.proposition,
                value: None,
                facts,
                obligations,
            });
        }
    }
    Ok(result)
}

/// A C `?:`, `&&` or `||` as the conditional it reads its operands under.
/// The condition, or the left side, is evaluated as an ordinary term; `?:`
/// claims its taken branch's root, and `&&` and `||` claim nothing of their
/// own: their right side is evaluated as an ordinary term only where the left
/// does not decide the result.
fn fragment_conditional(
    fragment: &ProgramExpression,
) -> Option<(SpecProposition, SpecExpression, SpecExpression)> {
    use crate::kernel::program_expression::int32_literal;
    let nonzero = |value: &ProgramExpression| SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(value.clone()),
        operator: ComparisonOperator::NotEqual,
        right: SpecExpression::ProgramExpression(int32_literal(0)),
    };
    // The right side evaluated as an ordinary term, owing its domain, under
    // a body that claims nothing.
    let truth = |value: &ProgramExpression| SpecExpression::Let {
        name: crate::kernel::GeneratedBinderId::fresh().binding_name(),
        value: Box::new(SpecExpression::ProgramExpression(value.clone())),
        body: Box::new(SpecExpression::ProgramExpression(int32_literal(1))),
    };
    match fragment {
        ProgramExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => Some((
            nonzero(condition),
            SpecExpression::ProgramExpression(then_branch.as_ref().clone()),
            SpecExpression::ProgramExpression(else_branch.as_ref().clone()),
        )),
        ProgramExpression::And(left, right) => Some((
            nonzero(left),
            truth(right),
            SpecExpression::ProgramExpression(int32_literal(0)),
        )),
        ProgramExpression::Or(left, right) => Some((
            nonzero(left),
            SpecExpression::ProgramExpression(int32_literal(1)),
            truth(right),
        )),
        _ => None,
    }
}

/// `body` with `value` in place of `name`, when `body` is `name` under
/// conversions only.
fn substitute_bound_result(
    name: &BindingName,
    value: &SpecExpression,
    body: &SpecExpression,
) -> Option<SpecExpression> {
    match body {
        SpecExpression::ProgramExpression(ProgramExpression::Variable(bound)) if bound == name => {
            Some(value.clone())
        }
        SpecExpression::Cast(inner, target) => Some(SpecExpression::Cast(
            Box::new(substitute_bound_result(name, value, inner)?),
            *target,
        )),
        SpecExpression::PointerCoercion(inner, target) => Some(SpecExpression::PointerCoercion(
            Box::new(substitute_bound_result(name, value, inner)?),
            *target,
        )),
        _ => None,
    }
}

/// One operand of a root operation: a machine value, an Integer, an
/// algebraic value, or a value inside a C fragment.
#[derive(Clone, Copy)]
enum Operand<'a> {
    Value(&'a SpecExpression),
    Integer(&'a SpecIntegerExpression),
    Algebraic(&'a SpecAlgebraicExpression),
    Fragment(&'a ProgramExpression),
}

/// An expression of an operand's kind that reads its evaluated value.
#[derive(Clone)]
enum Reference {
    Value(SpecExpression),
    Integer(SpecIntegerExpression),
    Algebraic(SpecAlgebraicExpression),
    Fragment(ProgramExpression),
}

impl Reference {
    fn value(self) -> SpecExpression {
        match self {
            Self::Value(value) => value,
            _ => unreachable!("a machine operand"),
        }
    }
    fn integer(self) -> SpecIntegerExpression {
        match self {
            Self::Integer(value) => value,
            _ => unreachable!("an Integer operand"),
        }
    }
    fn algebraic(self) -> SpecAlgebraicExpression {
        match self {
            Self::Algebraic(value) => value,
            _ => unreachable!("an algebraic operand"),
        }
    }
    fn fragment(self) -> ProgramExpression {
        match self {
            Self::Fragment(value) => value,
            _ => unreachable!("a C fragment operand"),
        }
    }
}

/// The operands of a root operation, in evaluation order. A form without
/// operand expressions has none and is evaluated whole.
fn operands(expression: &SpecExpression) -> Vec<Operand<'_>> {
    use SpecExpression as E;
    match expression {
        E::Add(left, right)
        | E::Subtract(left, right)
        | E::Multiply(left, right)
        | E::Divide(left, right)
        | E::Remainder(left, right)
        | E::ShiftLeft(left, right)
        | E::RustShiftLeft(left, right)
        | E::RustShiftRight(left, right)
        | E::ShiftRight(left, right)
        | E::BitwiseAnd(left, right)
        | E::BitwiseOr(left, right)
        | E::BitwiseXor(left, right) => vec![Operand::Value(left), Operand::Value(right)],
        E::Negate(operand) | E::BitwiseNot(operand) => vec![Operand::Value(operand)],
        // The format annotates the root operator itself.
        E::NarrowArithmetic(operator, _) => operands(operator),
        // Reached only where a conversion is the operation itself.
        E::Cast(operand, _) | E::PointerCoercion(operand, _) => vec![Operand::Value(operand)],
        E::MemoryLoad { pointer, .. } | E::Subobject { pointer, .. } => {
            vec![Operand::Value(pointer)]
        }
        E::PointerOffset {
            pointer, elements, ..
        } => vec![Operand::Value(pointer), Operand::Value(elements)],
        E::Requires { value, .. } => vec![Operand::Value(value)],
        E::SliceLength(slice) | E::SliceData(slice) => vec![Operand::Value(slice)],
        E::SliceFromRawParts { data, count } => vec![Operand::Value(data), Operand::Value(count)],
        E::IntegerToMachine { value, .. } => vec![Operand::Integer(value)],
        E::CountedResourceCount { arguments, .. } => {
            arguments.iter().flatten().map(Operand::Value).collect()
        }
        E::ObjectAddress(address) => vec![Operand::Value(&address.base)],
        // The fold's own domain includes every pass of its body; its bounds
        // and initial value are operands.
        E::RangeFold {
            start,
            end,
            initial,
            ..
        } => vec![
            Operand::Value(start),
            Operand::Value(end),
            Operand::Value(initial),
        ],
        // A by-value aggregate's field is a syntactic projection of the
        // parameter; its element indexes are the operands.
        E::AggregateFieldValue { pointer, .. } => {
            let mut indexes = Vec::new();
            projection_indexes(pointer, &mut indexes);
            indexes
        }
        E::PureFunctionApplication { arguments, .. } => {
            arguments.iter().filter_map(argument_operand).collect()
        }
        E::ProgramExpression(fragment) => fragment_operands(fragment),
        _ => Vec::new(),
    }
}

fn argument_operand(argument: &SpecPureFunctionArgument) -> Option<Operand<'_>> {
    match argument {
        SpecPureFunctionArgument::Value(value) => Some(Operand::Value(value)),
        SpecPureFunctionArgument::Integer(value) => Some(Operand::Integer(value)),
        SpecPureFunctionArgument::Algebraic(value) => Some(Operand::Algebraic(value)),
        SpecPureFunctionArgument::ObjectPointer { argument, .. } => argument_operand(argument),
        _ => None,
    }
}

fn replace_argument(
    argument: &SpecPureFunctionArgument,
    replacements: &mut impl Iterator<Item = Reference>,
) -> SpecPureFunctionArgument {
    let mut next = || replacements.next().expect("one replacement per operand");
    match argument {
        SpecPureFunctionArgument::Value(_) => SpecPureFunctionArgument::Value(next().value()),
        SpecPureFunctionArgument::Integer(_) => SpecPureFunctionArgument::Integer(next().integer()),
        SpecPureFunctionArgument::Algebraic(_) => {
            SpecPureFunctionArgument::Algebraic(next().algebraic())
        }
        SpecPureFunctionArgument::ObjectPointer {
            argument,
            object_class,
        } => SpecPureFunctionArgument::ObjectPointer {
            argument: Box::new(replace_argument(argument, replacements)),
            object_class: object_class.clone(),
        },
        argument => argument.clone(),
    }
}

/// The element indexes along a by-value aggregate's projection path.
fn projection_indexes<'a>(pointer: &'a SpecExpression, indexes: &mut Vec<Operand<'a>>) {
    match pointer {
        SpecExpression::PointerOffset {
            pointer, elements, ..
        } => {
            projection_indexes(pointer, indexes);
            indexes.push(Operand::Value(elements));
        }
        SpecExpression::Subobject { pointer, .. } => projection_indexes(pointer, indexes),
        _ => {}
    }
}

fn replace_projection_indexes(
    pointer: &SpecExpression,
    replacements: &mut impl Iterator<Item = Reference>,
) -> SpecExpression {
    match pointer {
        SpecExpression::PointerOffset {
            pointer,
            byte_width,
            ..
        } => {
            let pointer = replace_projection_indexes(pointer, replacements);
            SpecExpression::PointerOffset {
                pointer: Box::new(pointer),
                elements: Box::new(replacements.next().expect("an index").value()),
                byte_width: *byte_width,
            }
        }
        SpecExpression::Subobject { pointer, width } => SpecExpression::Subobject {
            pointer: Box::new(replace_projection_indexes(pointer, replacements)),
            width: *width,
        },
        pointer => pointer.clone(),
    }
}

/// The value operands of a C fragment's root operator. A place under `&`
/// keeps its shape; its indexes and the pointers it reads through are the
/// operands. `&&`, `||` and `?:` read an operand only under a guard and are
/// lowered by [`fragment_conditional`] instead.
fn fragment_operands(fragment: &ProgramExpression) -> Vec<Operand<'_>> {
    use ProgramExpression as P;
    match fragment {
        P::Add(left, right)
        | P::Subtract(left, right)
        | P::Multiply(left, right)
        | P::Divide(left, right)
        | P::Remainder(left, right)
        | P::ShiftLeft(left, right)
        | P::RustShiftLeft(left, right)
        | P::RustShiftRight(left, right)
        | P::ShiftRight(left, right)
        | P::BitwiseAnd(left, right)
        | P::BitwiseOr(left, right)
        | P::BitwiseXor(left, right)
        | P::LessThan(left, right)
        | P::LessEqual(left, right)
        | P::GreaterThan(left, right)
        | P::GreaterEqual(left, right)
        | P::Equal(left, right)
        | P::NotEqual(left, right) => vec![Operand::Fragment(left), Operand::Fragment(right)],
        P::Negate(operand)
        | P::FloatNegate(operand)
        | P::BitwiseNot(operand)
        | P::Not(operand)
        | P::Load(operand) => vec![Operand::Fragment(operand)],
        P::FloatClassification { expression, .. } => vec![Operand::Fragment(expression)],
        P::TypedLoad { pointer, .. }
        | P::PointerOffsetBytes { pointer, .. }
        | P::Subobject { pointer, .. } => vec![Operand::Fragment(pointer)],
        P::EnumField { value, .. } => vec![Operand::Fragment(value)],
        P::EnumConstruct { fields, .. } => fields.iter().map(Operand::Fragment).collect(),
        // A variable base names the object read; only the index is a value.
        P::Index(base, index) => {
            let mut operands = Vec::new();
            if !matches!(base.as_ref(), P::Variable(_)) {
                operands.push(Operand::Fragment(base));
            }
            operands.push(Operand::Fragment(index));
            operands
        }
        P::AddressOf(place) | P::CheckedObjectAddress(place) => {
            let mut operands = Vec::new();
            place_operands(place, &mut operands);
            operands
        }
        _ => Vec::new(),
    }
}

fn place_operands<'a>(place: &'a ProgramExpression, operands: &mut Vec<Operand<'a>>) {
    match place {
        ProgramExpression::Index(base, index) => {
            place_operands(base, operands);
            operands.push(Operand::Fragment(index));
        }
        ProgramExpression::Load(pointer) => operands.push(Operand::Fragment(pointer)),
        _ => {}
    }
}

fn replace_place(
    place: &ProgramExpression,
    replacements: &mut impl Iterator<Item = Reference>,
) -> ProgramExpression {
    match place {
        ProgramExpression::Index(base, _) => {
            let base = replace_place(base, replacements);
            ProgramExpression::Index(
                Box::new(base),
                Box::new(replacements.next().expect("an index").fragment()),
            )
        }
        ProgramExpression::Load(_) => {
            ProgramExpression::Load(Box::new(replacements.next().expect("a pointer").fragment()))
        }
        place => place.clone(),
    }
}

fn replace_fragment(
    fragment: &ProgramExpression,
    replacements: &mut impl Iterator<Item = Reference>,
) -> ProgramExpression {
    use ProgramExpression as P;
    let mut next = || {
        Box::new(
            replacements
                .next()
                .expect("one replacement per operand")
                .fragment(),
        )
    };
    match fragment {
        P::Add(..) => P::Add(next(), next()),
        P::Subtract(..) => P::Subtract(next(), next()),
        P::Multiply(..) => P::Multiply(next(), next()),
        P::Divide(..) => P::Divide(next(), next()),
        P::Remainder(..) => P::Remainder(next(), next()),
        P::ShiftLeft(..) => P::ShiftLeft(next(), next()),
        P::RustShiftLeft(..) => P::RustShiftLeft(next(), next()),
        P::RustShiftRight(..) => P::RustShiftRight(next(), next()),
        P::ShiftRight(..) => P::ShiftRight(next(), next()),
        P::BitwiseAnd(..) => P::BitwiseAnd(next(), next()),
        P::BitwiseOr(..) => P::BitwiseOr(next(), next()),
        P::BitwiseXor(..) => P::BitwiseXor(next(), next()),
        P::LessThan(..) => P::LessThan(next(), next()),
        P::LessEqual(..) => P::LessEqual(next(), next()),
        P::GreaterThan(..) => P::GreaterThan(next(), next()),
        P::GreaterEqual(..) => P::GreaterEqual(next(), next()),
        P::Equal(..) => P::Equal(next(), next()),
        P::NotEqual(..) => P::NotEqual(next(), next()),
        P::Negate(_) => P::Negate(next()),
        P::FloatNegate(_) => P::FloatNegate(next()),
        P::BitwiseNot(_) => P::BitwiseNot(next()),
        P::Not(_) => P::Not(next()),
        P::Load(_) => P::Load(next()),
        P::FloatClassification { classification, .. } => P::FloatClassification {
            expression: next(),
            classification: *classification,
        },
        P::TypedLoad {
            value_type,
            volatile,
            pointee_constant,
            access_class,
            source,
            ..
        } => P::TypedLoad {
            pointer: next(),
            value_type: *value_type,
            volatile: *volatile,
            pointee_constant: *pointee_constant,
            access_class: access_class.clone(),
            source: source.clone(),
        },
        P::PointerOffsetBytes { bytes, .. } => P::PointerOffsetBytes {
            pointer: next(),
            bytes: *bytes,
        },
        P::Subobject { width, .. } => P::Subobject {
            pointer: next(),
            width: *width,
        },
        P::EnumField { variant, index, .. } => P::EnumField {
            value: next(),
            variant: variant.clone(),
            index: *index,
        },
        P::EnumConstruct {
            enum_type,
            variant,
            fields,
        } => P::EnumConstruct {
            enum_type: *enum_type,
            variant: variant.clone(),
            fields: fields.iter().map(|_| *next()).collect(),
        },
        P::Index(base, _) => {
            let base = if matches!(base.as_ref(), P::Variable(_)) {
                base.clone()
            } else {
                next()
            };
            P::Index(base, next())
        }
        P::AddressOf(place) => P::AddressOf(Box::new(replace_place(place, replacements))),
        P::CheckedObjectAddress(place) => {
            P::CheckedObjectAddress(Box::new(replace_place(place, replacements)))
        }
        fragment => fragment.clone(),
    }
}

/// `expression` with each operand, in [`operands`] order, replaced by the
/// next of `replacements`.
fn replace_operands(
    expression: &SpecExpression,
    replacements: &mut impl Iterator<Item = Reference>,
) -> SpecExpression {
    use SpecExpression as E;
    let mut next = || {
        Box::new(
            replacements
                .next()
                .expect("one replacement per operand")
                .value(),
        )
    };
    match expression {
        E::Add(..) => E::Add(next(), next()),
        E::Subtract(..) => E::Subtract(next(), next()),
        E::Multiply(..) => E::Multiply(next(), next()),
        E::Divide(..) => E::Divide(next(), next()),
        E::Remainder(..) => E::Remainder(next(), next()),
        E::ShiftLeft(..) => E::ShiftLeft(next(), next()),
        E::RustShiftLeft(..) => E::RustShiftLeft(next(), next()),
        E::RustShiftRight(..) => E::RustShiftRight(next(), next()),
        E::ShiftRight(..) => E::ShiftRight(next(), next()),
        E::BitwiseAnd(..) => E::BitwiseAnd(next(), next()),
        E::BitwiseOr(..) => E::BitwiseOr(next(), next()),
        E::BitwiseXor(..) => E::BitwiseXor(next(), next()),
        E::Negate(_) => E::Negate(next()),
        E::BitwiseNot(_) => E::BitwiseNot(next()),
        E::Cast(_, target) => E::Cast(next(), *target),
        E::PointerCoercion(_, target) => E::PointerCoercion(next(), *target),
        E::SliceLength(_) => E::SliceLength(next()),
        E::SliceData(_) => E::SliceData(next()),
        E::SliceFromRawParts { .. } => E::SliceFromRawParts {
            data: next(),
            count: next(),
        },
        E::NarrowArithmetic(operator, format) => {
            E::NarrowArithmetic(Box::new(replace_operands(operator, replacements)), *format)
        }
        E::MemoryLoad {
            point,
            value_type,
            exact,
            ..
        } => E::MemoryLoad {
            point: point.clone(),
            pointer: next(),
            value_type: *value_type,
            exact: *exact,
        },
        E::Subobject { width, .. } => E::Subobject {
            pointer: next(),
            width: *width,
        },
        E::PointerOffset { byte_width, .. } => {
            let pointer = next();
            E::PointerOffset {
                pointer,
                elements: next(),
                byte_width: *byte_width,
            }
        }
        E::Requires { requirement, .. } => E::Requires {
            requirement: requirement.clone(),
            value: next(),
        },
        E::IntegerToMachine { destination, .. } => E::IntegerToMachine {
            value: Box::new(replacements.next().expect("an Integer operand").integer()),
            destination: *destination,
        },
        E::CountedResourceCount { name, arguments } => E::CountedResourceCount {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| argument.as_ref().map(|_| *next()))
                .collect(),
        },
        E::ObjectAddress(address) => {
            let mut address = address.as_ref().clone();
            address.base = next();
            E::ObjectAddress(Box::new(address))
        }
        E::RangeFold {
            accumulator,
            item,
            body,
            ..
        } => {
            let start = next();
            let end = next();
            E::RangeFold {
                start,
                end,
                initial: next(),
                accumulator: accumulator.clone(),
                item: item.clone(),
                body: body.clone(),
            }
        }
        E::AggregateFieldValue {
            parameter,
            pointer,
            value_type,
        } => E::AggregateFieldValue {
            parameter: parameter.clone(),
            pointer: Box::new(replace_projection_indexes(pointer, replacements)),
            value_type: *value_type,
        },
        E::PureFunctionApplication {
            name,
            arguments,
            result_type,
            pointer_result,
            result_object_class,
        } => E::PureFunctionApplication {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| replace_argument(argument, replacements))
                .collect(),
            result_type: *result_type,
            pointer_result: pointer_result.clone(),
            result_object_class: result_object_class.clone(),
        },
        E::ProgramExpression(fragment) => {
            E::ProgramExpression(replace_fragment(fragment, replacements))
        }
        expression => expression.clone(),
    }
}

/// A prefix of evaluated operands: their values bound to fresh names, and
/// the facts and obligations their evaluation produced.
#[derive(Clone)]
struct Operands {
    state: ExecutionState,
    values: crate::persistent::PersistentMap<BindingName, KernelTerm>,
    algebraic: BTreeMap<BindingName, AlgebraicTerm>,
    integers: Vec<(Variable, IntegerResult)>,
    references: Vec<Reference>,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    context: PureFactContext,
}

/// An operand path: what one evaluation of an operand produced.
struct OperandPath {
    reference: Reference,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
}

/// Evaluate one operand as an ordinary term and give each path's value a
/// reference that owes nothing, binding it in `prefix` where it needs a name.
fn operand_paths(
    scope: SpecScope<'_>,
    operand: Operand<'_>,
    prefix: &mut Operands,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<(Operands, OperandPath)>> {
    let mut result = Vec::new();
    match operand {
        Operand::Value(value) => {
            for path in evaluate_spec_expression_paths_with_algebraic_bindings_in(
                scope,
                value,
                &prefix.context,
                budget,
            )? {
                let mut next = prefix.clone();
                let reference = operand_reference(path.value, &mut next.state, &mut next.values);
                result.push((
                    next,
                    OperandPath {
                        reference: Reference::Value(reference),
                        facts: path.facts,
                        obligations: path.obligations,
                    },
                ));
            }
        }
        Operand::Fragment(fragment) => {
            for path in evaluate_spec_expression_paths_with_algebraic_bindings_in(
                scope,
                &SpecExpression::ProgramExpression(fragment.clone()),
                &prefix.context,
                budget,
            )? {
                let next = prefix.clone();
                // A C fragment reads its operands as C values, not names: the
                // operand's value is substituted natively.
                let reference = ProgramExpression::Value(path.value.into_native());
                result.push((
                    next,
                    OperandPath {
                        reference: Reference::Fragment(reference),
                        facts: path.facts,
                        obligations: path.obligations,
                    },
                ));
            }
        }
        Operand::Integer(value) => {
            for path in
                evaluate_spec_integer_expression_paths_in(scope, value, &prefix.context, budget)?
            {
                let mut next = prefix.clone();
                // Bound only while the root is evaluated, and substituted by
                // its value there, so a binder identity serves; proof-side
                // evaluation may not invent an execution identity.
                let variable = budget.allocate_match_binder_variable()?;
                next.integers.push((variable, path.value));
                result.push((
                    next,
                    OperandPath {
                        reference: Reference::Integer(SpecIntegerExpression::Term(
                            IntegerTerm::Variable(variable),
                        )),
                        facts: path.facts,
                        obligations: path.obligations,
                    },
                ));
            }
        }
        Operand::Algebraic(value) => {
            for path in evaluate_spec_algebraic_at_state_with_bindings_in(
                scope,
                value,
                &prefix.context,
                budget,
            )? {
                let mut next = prefix.clone();
                let name = crate::kernel::GeneratedBinderId::fresh().binding_name();
                let algebraic_type = value.algebraic_type.clone();
                next.algebraic
                    .insert(name.clone(), path.value.into_native_compat());
                result.push((
                    next,
                    OperandPath {
                        reference: Reference::Algebraic(SpecAlgebraicExpression {
                            algebraic_type,
                            node: SpecAlgebraicExpressionNode::Binding(name),
                        }),
                        facts: path.facts,
                        obligations: path.obligations,
                    },
                ));
            }
        }
    }
    Ok(result)
}

fn operation(
    scope: SpecScope<'_>,
    expression: &SpecExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<DefinedPath>> {
    let operand_expressions = operands(expression);
    // Operands that are already values owe nothing and need no binding: the
    // root evaluated as written is the same evaluation.
    if operand_expressions.iter().all(|operand| {
        matches!(
            operand,
            Operand::Value(SpecExpression::Value(_))
                | Operand::Fragment(ProgramExpression::Value(_))
        )
    }) {
        return Ok(vec![root(
            scope,
            expression,
            &[],
            ExecutionFacts::new(),
            Vec::new(),
            assumptions,
            budget,
        )?]);
    }
    let mut prefixes = vec![Operands {
        state: scope.state.clone(),
        values: scope.values.cloned().unwrap_or_default(),
        algebraic: scope.algebraic_bindings.clone(),
        integers: Vec::new(),
        references: Vec::new(),
        facts: ExecutionFacts::new(),
        obligations: Vec::new(),
        context: assumptions.clone(),
    }];
    for operand in operand_expressions {
        let mut extended = Vec::new();
        for mut prefix in prefixes {
            for (mut next, path) in operand_paths(scope, operand, &mut prefix, budget)? {
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations_under(
                    &prefix.facts,
                    &prefix.obligations,
                    &path.facts,
                    &path.obligations,
                    assumptions,
                    &prefix.context,
                ) else {
                    continue;
                };
                next.context = assumptions_with_path_context(assumptions, &facts, &obligations);
                next.facts = facts;
                next.obligations = obligations;
                next.references.push(path.reference);
                extended.push(next);
            }
        }
        prefixes = extended;
    }
    let mut result = Vec::new();
    for prefix in prefixes {
        let root_expression = replace_operands(expression, &mut prefix.references.into_iter());
        let root_scope = SpecScope {
            state: &prefix.state,
            values: Some(&prefix.values),
            algebraic_bindings: &prefix.algebraic,
            ..scope
        };
        result.push(root(
            root_scope,
            &root_expression,
            &prefix.integers,
            prefix.facts,
            prefix.obligations,
            assumptions,
            budget,
        )?);
    }
    Ok(result)
}

/// An expression that reads an evaluated operand's value and owes nothing. A
/// native value, and a shared pointer through its retained native pointer, is
/// that value itself, which keeps its C type, including a pointer's provenance
/// and element width. Any other shared root is bound to a fresh generated
/// name, which reads that same root.
fn operand_reference(
    value: SpecValue,
    state: &mut ExecutionState,
    values: &mut crate::persistent::PersistentMap<BindingName, KernelTerm>,
) -> SpecExpression {
    match value {
        SpecValue::Native(value) => SpecExpression::Value(value),
        // A pointer's arithmetic reads its element width from its type, which
        // its retained native pointer keeps and a generated name does not.
        SpecValue::Shared(root) if root.old_pointer_value().is_some() => {
            SpecExpression::Value(SpecValue::Shared(root).into_native())
        }
        value => {
            let name = crate::kernel::GeneratedBinderId::fresh().binding_name();
            bindings::bind_value(&name, value, state, values);
            SpecExpression::ProgramExpression(ProgramExpression::Variable(name))
        }
    }
}

/// Evaluate a root over already-evaluated operands, from no facts and with
/// C's evaluation rules. Its conditions are the claim; the operands' facts
/// and obligations are carried unchanged.
fn root(
    scope: SpecScope<'_>,
    expression: &SpecExpression,
    integers: &[(Variable, IntegerResult)],
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<DefinedPath> {
    // The root reads the caller's Integer binders and its own operands'.
    let mut bindings = budget.integer_bindings.clone();
    bindings.extend(integers.iter().cloned());
    let mut checked = SpecEvaluation::checked(budget);
    checked.program_definedness = true;
    checked.integer_bindings = bindings;
    let paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
        scope,
        expression,
        &definedness_context(assumptions),
        &mut checked,
    )?;
    let value = match paths.as_slice() {
        [path] => Some(path.value.clone()),
        _ => None,
    };
    Ok(DefinedPath {
        claim: definedness_claim(paths),
        value,
        facts,
        obligations,
    })
}

/// A conversion to its operand's own type is no operation: the claim is the
/// operand's. Any other conversion is the root operation, and the operand's
/// claim is owed like any operand's domain.
fn conversion(
    scope: SpecScope<'_>,
    expression: &SpecExpression,
    operand: &SpecExpression,
    target: ProgramType,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<DefinedPath>> {
    let mut result = Vec::new();
    for inner in paths(scope, operand, assumptions, budget)? {
        let Some(value) = inner.value.clone() else {
            // Several root values: evaluate the conversion as an operation.
            result.extend(operation(scope, expression, assumptions, budget)?);
            continue;
        };
        if value.program_type() == target {
            result.push(inner);
            continue;
        }
        let mut obligations = inner.obligations;
        if !is_true(&inner.claim) {
            obligations.push(ProofObligation::evaluation_domain(inner.claim));
        }
        let mut state = scope.state.clone();
        let mut values = scope.values.cloned().unwrap_or_default();
        let reference = operand_reference(value, &mut state, &mut values);
        let root_expression = replace_conversion_operand(expression, reference);
        result.push(root(
            SpecScope {
                state: &state,
                values: Some(&values),
                ..scope
            },
            &root_expression,
            &[],
            inner.facts,
            obligations,
            assumptions,
            budget,
        )?);
    }
    Ok(result)
}

fn replace_conversion_operand(
    expression: &SpecExpression,
    operand: SpecExpression,
) -> SpecExpression {
    match expression {
        SpecExpression::Cast(_, target) => SpecExpression::Cast(Box::new(operand), *target),
        SpecExpression::PointerCoercion(_, target) => {
            SpecExpression::PointerCoercion(Box::new(operand), *target)
        }
        _ => unreachable!("a conversion"),
    }
}

fn is_true(proposition: &Proposition) -> bool {
    proposition.literal_condition() == Some((true, true))
}

fn negation(proposition: &Proposition) -> Proposition {
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            Proposition::ConditionIs(condition.clone(), !value)
        }
        proposition => Proposition::Not(Box::new(proposition.clone())),
    }
}

/// `if c { x } else { y }` reads only its selected branch: the claim is
/// `(c implies defined(x)) and (not c implies defined(y))`, and each branch's
/// obligations are owed only under its own side of the condition.
/// `(holds implies then) and (fails implies else)`, where a branch that
/// claims nothing contributes nothing.
fn guarded_claim(
    holds: &Proposition,
    then_claim: &Proposition,
    fails: &Proposition,
    else_claim: &Proposition,
) -> Proposition {
    let implication = |guard: &Proposition, claim: &Proposition| {
        (!is_true(claim))
            .then(|| Proposition::Implies(Box::new(guard.clone()), Box::new(claim.clone())))
    };
    match (
        implication(holds, then_claim),
        implication(fails, else_claim),
    ) {
        (Some(left), Some(right)) => Proposition::And(Box::new(left), Box::new(right)),
        (Some(claim), None) | (None, Some(claim)) => claim,
        (None, None) => then_claim.clone(),
    }
}

fn conditional(
    scope: SpecScope<'_>,
    condition: &SpecProposition,
    then_branch: &SpecExpression,
    else_branch: &SpecExpression,
    assumptions: &PureFactContext,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Vec<DefinedPath>> {
    let mut result = Vec::new();
    for condition_path in lower_spec_proposition_at_state_with_algebraic_bindings_in(
        scope,
        condition,
        assumptions,
        budget,
    )? {
        let context = assumptions_with_path_context(
            assumptions,
            &condition_path.facts,
            &condition_path.obligations,
        );
        let holds = condition_path.proposition.clone();
        let fails = negation(&holds);
        let then_paths = paths(
            scope,
            then_branch,
            &context.clone().assume_proposition(holds.clone()),
            budget,
        )?;
        let else_paths = paths(
            scope,
            else_branch,
            &context.clone().assume_proposition(fails.clone()),
            budget,
        )?;
        for then_path in &then_paths {
            for else_path in &else_paths {
                let mut guarded = guard_right_obligations(&holds, then_path.obligations.clone());
                guarded.extend(guard_right_obligations(
                    &fails,
                    else_path.obligations.clone(),
                ));
                // Each branch's path conditions are owed where it is taken.
                let mut branch_facts = guard_right_facts(&holds, &then_path.facts, &mut guarded);
                branch_facts.extend_shared(&guard_right_facts(
                    &fails,
                    &else_path.facts,
                    &mut guarded,
                ));
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations_under(
                    &condition_path.facts,
                    &condition_path.obligations,
                    &branch_facts,
                    &guarded,
                    assumptions,
                    &context,
                ) else {
                    continue;
                };
                result.push(DefinedPath {
                    claim: guarded_claim(&holds, &then_path.claim, &fails, &else_path.claim),
                    value: None,
                    facts,
                    obligations,
                });
            }
        }
    }
    Ok(result)
}

#[cfg(test)]
#[path = "operation_defined_tests.rs"]
mod tests;
