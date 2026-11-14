//! Where in a refused statement its undefined behavior arises.
//!
//! A statement transition reports undefined behavior by kind only. When a
//! step is refused for it, the diagnostic names the operation as well: the
//! statement's expressions are evaluated again at its entry state, innermost
//! first, and the first one whose own evaluation has a path with the same
//! kind is the site. This runs only to word a refusal, never while checking.

use super::*;

/// The part of a statement whose evaluation has the reported undefined
/// behavior.
#[derive(Clone, Debug)]
pub(crate) enum CUndefinedBehaviorSite {
    /// An expression the statement evaluates.
    Expression(ProgramExpression),
    /// The store through this pointer expression, when no operand of the
    /// store has the behavior itself.
    Store(ProgramExpression),
}

/// The innermost operation of `statement` that has `kind` at `state`, or
/// `None` when no single operation can be named.
///
/// The search never descends into an operand that a guard decides whether
/// to evaluate (the right side of `&&` and `||`, the arms of `?:`), nor
/// into the place an `&` names, so it never blames an operation the
/// statement does not run. Such an operand is reported through the
/// expression that contains it.
pub(crate) fn locate_undefined_behavior(
    state: &ExecutionState,
    statement: &ProgramStatement,
    assumptions: &PureFactContext,
    kind: &CUndefinedBehavior,
) -> Option<CUndefinedBehaviorSite> {
    let mut expressions = Vec::new();
    statement_expressions(statement, &mut expressions);
    for (expression, condition) in expressions {
        if let Some(site) = innermost_site(state, expression, condition, assumptions, kind) {
            return Some(CUndefinedBehaviorSite::Expression(site.clone()));
        }
    }
    match statement {
        ProgramStatement::Store { pointer, .. } | ProgramStatement::TypedStore { pointer, .. } => {
            Some(CUndefinedBehaviorSite::Store(pointer.clone()))
        }
        _ => None,
    }
}

/// [`locate_undefined_behavior`] for a controlling expression evaluated on
/// its own, as a branch or loop condition is.
pub(crate) fn locate_undefined_behavior_in_condition(
    state: &ExecutionState,
    condition: &ProgramExpression,
    assumptions: &PureFactContext,
    kind: &CUndefinedBehavior,
) -> Option<CUndefinedBehaviorSite> {
    innermost_site(state, condition, true, assumptions, kind)
        .map(|site| CUndefinedBehaviorSite::Expression(site.clone()))
}

/// The expressions `statement` evaluates itself, each with whether its value
/// is tested for truth. Nested statement bodies are not stepped with it.
pub(super) fn statement_expressions<'a>(
    statement: &'a ProgramStatement,
    expressions: &mut Vec<(&'a ProgramExpression, bool)>,
) {
    match statement {
        ProgramStatement::Declare {
            initializer: Some(expression),
            ..
        }
        | ProgramStatement::Assign { expression, .. }
        | ProgramStatement::HeapAllocate {
            bytes: expression, ..
        }
        | ProgramStatement::HeapFree {
            pointer: expression,
        }
        | ProgramStatement::Return(expression)
        | ProgramStatement::Throw(expression)
        | ProgramStatement::Switch { expression, .. } => expressions.push((expression, false)),
        ProgramStatement::Assert { condition, .. }
        | ProgramStatement::LoopTest { condition }
        | ProgramStatement::If { condition, .. }
        | ProgramStatement::While { condition, .. } => expressions.push((condition, true)),
        ProgramStatement::CallAssign { arguments, .. }
        | ProgramStatement::Call { arguments, .. }
        | ProgramStatement::CallResult { arguments, .. } => {
            expressions.extend(arguments.iter().map(|argument| (argument, false)));
        }
        ProgramStatement::Store { pointer, value }
        | ProgramStatement::TypedStore { pointer, value, .. } => {
            expressions.push((pointer, false));
            expressions.push((value, false));
        }
        ProgramStatement::CopyAggregate { target, source, .. }
        | ProgramStatement::InitializeScalarArray { target, source, .. } => {
            expressions.push((target, false));
            expressions.push((source, false));
        }
        ProgramStatement::Update { operand, .. } => expressions.push((operand, false)),
        ProgramStatement::ForStep { step, .. } => statement_expressions(step, expressions),
        ProgramStatement::Seq(statements) => statement_expressions(statements.first(), expressions),
        ProgramStatement::Skip
        | ProgramStatement::EndScalarReference(_)
        | ProgramStatement::ScalarReferenceScope(_)
        | ProgramStatement::Break
        | ProgramStatement::Continue
        | ProgramStatement::Goto { .. }
        | ProgramStatement::Declare {
            initializer: None, ..
        }
        | ProgramStatement::DeclareAggregate { .. }
        | ProgramStatement::TryCatchInt32 { .. }
        | ProgramStatement::EndAutomaticLifetimes { .. } => {}
    }
}

fn innermost_site<'a>(
    state: &ExecutionState,
    expression: &'a ProgramExpression,
    condition: bool,
    assumptions: &PureFactContext,
    kind: &CUndefinedBehavior,
) -> Option<&'a ProgramExpression> {
    let mut children = Vec::new();
    unconditional_operands(expression, &mut children);
    for child in children {
        if let Some(site) = innermost_site(state, child, false, assumptions, kind) {
            return Some(site);
        }
    }
    has_undefined_behavior(state, expression, condition, assumptions, kind).then_some(expression)
}

fn has_undefined_behavior(
    state: &ExecutionState,
    expression: &ProgramExpression,
    condition: bool,
    assumptions: &PureFactContext,
    kind: &CUndefinedBehavior,
) -> bool {
    let mut budget = ExecutionBudget::beside_live_state();
    let paths = if condition {
        evaluate_c_condition_paths(state, expression, assumptions, &mut budget)
    } else {
        evaluate_c_expression_paths(state, expression, assumptions, &mut budget)
    };
    paths.is_ok_and(|paths| {
        paths.iter().any(|path| {
            matches!(&path.outcome, CExpressionOutcome::UndefinedBehavior(found)
                if std::mem::discriminant(found) == std::mem::discriminant(kind))
        })
    })
}

/// The operands of `expression` that are evaluated whenever it is.
fn unconditional_operands<'a>(
    expression: &'a ProgramExpression,
    operands: &mut Vec<&'a ProgramExpression>,
) {
    match expression {
        ProgramExpression::Value(_)
        | ProgramExpression::Variable(_)
        | ProgramExpression::FunctionAddress(_)
        | ProgramExpression::CallResult { .. } => {}
        ProgramExpression::Cast { expression, .. }
        | ProgramExpression::FloatNegate(expression)
        | ProgramExpression::FloatClassification { expression, .. }
        | ProgramExpression::EnumField {
            value: expression, ..
        }
        | ProgramExpression::EnumIs {
            value: expression, ..
        }
        | ProgramExpression::Not(expression)
        | ProgramExpression::BitwiseNot(expression)
        | ProgramExpression::Load(expression)
        | ProgramExpression::TypedLoad {
            pointer: expression,
            ..
        }
        | ProgramExpression::PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | ProgramExpression::Subobject {
            pointer: expression,
            ..
        } => operands.push(expression),
        ProgramExpression::Conditional { condition, .. } => operands.push(condition),
        ProgramExpression::EnumConstruct { fields, .. } => operands.extend(fields),
        ProgramExpression::And(left, _) | ProgramExpression::Or(left, _) => operands.push(left),
        ProgramExpression::AddressOf(place) | ProgramExpression::CheckedObjectAddress(place) => {
            place_address_operands(place, operands);
        }
        ProgramExpression::LessThan(left, right)
        | ProgramExpression::LessEqual(left, right)
        | ProgramExpression::GreaterThan(left, right)
        | ProgramExpression::GreaterEqual(left, right)
        | ProgramExpression::Equal(left, right)
        | ProgramExpression::NotEqual(left, right)
        | ProgramExpression::Add(left, right)
        | ProgramExpression::Subtract(left, right)
        | ProgramExpression::Multiply(left, right)
        | ProgramExpression::Divide(left, right)
        | ProgramExpression::Remainder(left, right)
        | ProgramExpression::ShiftLeft(left, right)
        | ProgramExpression::RustShiftLeft(left, right)
        | ProgramExpression::ShiftRight(left, right)
        | ProgramExpression::RustShiftRight(left, right)
        | ProgramExpression::BitwiseAnd(left, right)
        | ProgramExpression::BitwiseOr(left, right)
        | ProgramExpression::BitwiseXor(left, right)
        | ProgramExpression::Index(left, right) => {
            operands.push(left);
            operands.push(right);
        }
    }
}

/// The operands evaluated to form the address of `place` without reading
/// it: the pointer of `*p`, and the base and index of `a[i]`.
fn place_address_operands<'a>(
    place: &'a ProgramExpression,
    operands: &mut Vec<&'a ProgramExpression>,
) {
    match place {
        ProgramExpression::Load(pointer) | ProgramExpression::TypedLoad { pointer, .. } => {
            operands.push(pointer);
        }
        ProgramExpression::Index(base, index) => {
            operands.push(base);
            operands.push(index);
        }
        _ => {}
    }
}
