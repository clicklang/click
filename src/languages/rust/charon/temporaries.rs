//! MIR's pure temporaries, put back into the expressions that read them.
//!
//! MIR is three-address code: `x = a + b * c` stores `b * c` in a local of
//! its own before adding it to `a`. That local is part of the expression, not
//! a variable of the program, and a proof should never see it. A local the
//! source does not name, assigned once from a pure value and read once later
//! in the same block, with nothing between the two that could change what the
//! value reads, is substituted into its read and removed: the expression is
//! `a + b * c` again.
//!
//! A value with a checked operator moves only into a read whose lowering
//! emits that operator's panic check (`substitute`). A temporary stays when
//! it is:
//! - assigned more than once, or read more than once or across blocks;
//! - named by a statement rather than read by an expression;
//! - the storage of a place, as in `&t`, `t.f` or `t[i]`;
//! - an enum `match` scrutinee;
//! - assigned a call, a borrow or an indexed place.

use super::super::schema::{
    Expression as E, MirBlock, MirStatement as S, MirTerminator as T, Place,
};
use std::collections::{BTreeMap, BTreeSet};

/// Substitutes each pure temporary of `temporaries` into its one read, and
/// removes it from `locals` and its block.
pub(super) fn substitute_pure_values(
    locals: &mut Vec<Place>,
    blocks: &mut [MirBlock],
    temporaries: &BTreeSet<String>,
) {
    // How each temporary is used: read by an expression, or named by a
    // statement or terminator field, which no substitution can reach.
    let mut reads = BTreeMap::<String, usize>::new();
    let mut named = BTreeSet::<String>::new();
    let mut assignments = BTreeMap::<String, usize>::new();
    for block in blocks.iter() {
        for statement in &block.statements {
            statement_uses(statement, &mut reads, &mut named);
            if let S::Assign {
                target: E::Local { name },
                ..
            } = statement
            {
                *assignments.entry(name.clone()).or_default() += 1;
            }
        }
        terminator_uses(&block.terminator, &mut reads, &mut named);
        if let Some(destination) = call_destination(&block.terminator) {
            named.insert(destination.clone());
        }
    }
    let substitutable = |name: &str| {
        temporaries.contains(name)
            && !named.contains(name)
            && reads.get(name) == Some(&1)
            && assignments.get(name) == Some(&1)
    };
    let mut removed = BTreeSet::new();
    for block in blocks.iter_mut() {
        // The pure values defined so far in this block whose read is still
        // ahead, with nothing since that could change them.
        let mut pending = BTreeMap::<String, E>::new();
        let mut kept = Vec::with_capacity(block.statements.len());
        for mut statement in std::mem::take(&mut block.statements) {
            for (name, value) in substitute_statement(&mut statement, &mut pending) {
                removed.remove(&name);
                kept.push(S::Assign {
                    target: E::Local { name },
                    value,
                });
            }
            match &statement {
                S::Assign {
                    target: E::Local { name },
                    value,
                } if substitutable(name) && pure(value) => {
                    pending.insert(name.clone(), value.clone());
                    removed.insert(name.clone());
                    continue;
                }
                S::BeginStorage { .. }
                | S::EndStorage { .. }
                | S::Assert { .. }
                | S::Site { .. } => {}
                _ => {
                    // Anything else may change what a pending value reads,
                    // so no pending value moves past it: its definition goes
                    // back just before this statement, past nothing but
                    // storage markers, checks and other pure definitions.
                    for (name, value) in std::mem::take(&mut pending) {
                        removed.remove(&name);
                        kept.push(S::Assign {
                            target: E::Local { name },
                            value,
                        });
                    }
                }
            }
            kept.push(statement);
        }
        for (name, value) in substitute_terminator(&mut block.terminator, &mut pending) {
            removed.remove(&name);
            kept.push(S::Assign {
                target: E::Local { name },
                value,
            });
        }
        block.statements = kept;
        // A value whose read is not in this block stays a temporary.
        for (name, value) in pending {
            removed.remove(&name);
            block.statements.push(S::Assign {
                target: E::Local { name },
                value,
            });
        }
    }
    for block in blocks.iter_mut() {
        block.statements.retain(|statement| match statement {
            S::BeginStorage { local } | S::EndStorage { local } => !removed.contains(local),
            _ => true,
        });
    }
    locals.retain(|local| !removed.contains(&local.name));
}

/// The local a call terminator assigns its result to, unless the call is
/// already a call step.
fn call_destination(terminator: &T) -> Option<&String> {
    match terminator {
        T::Call {
            destination,
            result: None,
            ..
        } => Some(destination),
        _ => None,
    }
}

/// Makes each call whose result only one later expression reads a call
/// step: the call's `result` is a step number, and the read is
/// `Expression::CallResult` of it, the value of the expression that holds
/// the call. The destination must be a temporary of `temporaries` of scalar
/// or enum type, assigned by nothing but this call and read once, in the call's
/// successor, which only this call reaches. Every other call keeps its
/// destination.
pub(super) fn call_steps(
    locals: &mut Vec<Place>,
    blocks: &mut [MirBlock],
    temporaries: &BTreeSet<String>,
) {
    let mut reads = BTreeMap::<String, usize>::new();
    let mut named = BTreeSet::<String>::new();
    let mut assigned = BTreeMap::<String, usize>::new();
    let mut predecessors = vec![0usize; blocks.len()];
    for block in blocks.iter() {
        for statement in &block.statements {
            statement_uses(statement, &mut reads, &mut named);
            if let S::Assign {
                target: E::Local { name },
                ..
            } = statement
            {
                *assigned.entry(name.clone()).or_default() += 1;
            }
        }
        terminator_uses(&block.terminator, &mut reads, &mut named);
        if let Some(destination) = call_destination(&block.terminator) {
            *assigned.entry(destination.clone()).or_default() += 1;
        }
        for target in successors(&block.terminator) {
            if let Some(count) = predecessors.get_mut(target) {
                *count += 1;
            }
        }
    }
    let scalar = |name: &str| {
        locals.iter().any(|local| {
            local.name == name
                && (local.value_type == super::super::schema::Type::Bool
                    || local.value_type.integer_bits().is_some()
                    || matches!(local.value_type, super::super::schema::Type::Enum { .. }))
        })
    };
    let mut removed = BTreeSet::new();
    let mut next_step = 0u32;
    for index in 0..blocks.len() {
        let T::Call {
            function,
            destination,
            target,
            through_pointer: false,
            result: None,
            ..
        } = &blocks[index].terminator
        else {
            continue;
        };
        let (function, destination, target) = (function.clone(), destination.clone(), *target);
        if !temporaries.contains(&destination)
            || named.contains(&destination)
            || reads.get(&destination) != Some(&1)
            || assigned.get(&destination) != Some(&1)
            || !scalar(&destination)
            || target == index
            || predecessors.get(target) != Some(&1)
        {
            continue;
        }
        let call = next_step;
        let mut values = BTreeMap::from([(destination.clone(), E::CallResult { call, function })]);
        let mut pending = Pending {
            values: &mut values,
            refused: Vec::new(),
        };
        let successor = &mut blocks[target];
        for statement in &mut successor.statements {
            for expression in statement_expressions_mut(statement) {
                substitute(expression, &mut pending, true);
            }
            if let S::Assign { target, .. } = statement {
                substitute_target(target, &mut pending);
            }
        }
        for expression in terminator_expressions_mut(&mut successor.terminator) {
            substitute(expression, &mut pending, true);
        }
        // Its one read is elsewhere: the call keeps its destination.
        if !values.is_empty() {
            continue;
        }
        if let T::Call { result, .. } = &mut blocks[index].terminator {
            *result = Some(call);
        }
        next_step += 1;
        removed.insert(destination);
    }
    for block in blocks.iter_mut() {
        block.statements.retain(|statement| match statement {
            S::BeginStorage { local } | S::EndStorage { local } => !removed.contains(local),
            _ => true,
        });
    }
    locals.retain(|local| !removed.contains(&local.name));
}

fn successors(terminator: &T) -> Vec<usize> {
    match terminator {
        T::Goto { target }
        | T::Drop { target, .. }
        | T::Call { target, .. }
        | T::BoxNew { target, .. }
        | T::BoxFree { target, .. } => vec![*target],
        T::If {
            then_target,
            else_target,
            ..
        } => vec![*then_target, *else_target],
        T::Switch {
            cases, otherwise, ..
        } => cases
            .iter()
            .map(|case| case.target)
            .chain(*otherwise)
            .collect(),
        T::Return | T::Unreachable | T::Panic { .. } => Vec::new(),
    }
}

/// Whether evaluating `value` has no effect and may move to a later point in
/// its block with nothing between that changes what it reads.
fn pure(value: &E) -> bool {
    match value {
        E::Integer { .. }
        | E::UnsignedInteger { .. }
        | E::SignedInteger { .. }
        | E::UsizeInteger { .. }
        | E::Boolean { .. }
        | E::NoneBox
        | E::Local { .. }
        | E::FunctionAddress { .. }
        | E::CallResult { .. } => true,
        E::IntegerFrom { value, .. }
        | E::Not { value }
        | E::BitwiseNot { value, .. }
        | E::Cast { value, .. } => pure(value),
        E::Binary { left, right, .. } => pure(left) && pure(right),
        E::Deref { reference, .. } => pure(reference),
        E::Field { base, .. } | E::EnumField { base, .. } => pure(base),
        E::EnumConstruct { fields, .. } => fields.iter().all(pure),
        E::SliceLength { slice } => pure(slice),
        // A call has effects; a borrow begins a loan; an indexed place and
        // the iterator protocol need their own checked preparation.
        E::Call { .. }
        | E::Borrow { .. }
        | E::Index { .. }
        | E::ArrayToSlice { .. }
        | E::Array { .. }
        | E::Repeat { .. }
        | E::ClosureInstance { .. }
        | E::SharedArrayHasNext { .. }
        | E::EnumerateOptionIndex { .. }
        | E::RangeHasNext { .. }
        | E::SharedArrayOptionElement { .. }
        | E::SharedArrayOptionTag { .. }
        | E::ChunkHasNext { .. }
        | E::ChunkOptionSlice { .. }
        | E::ChunkOptionTag { .. }
        | E::ChunkRemainder { .. } => false,
    }
}

/// Each expression a statement evaluates, mutably.
fn statement_expressions_mut(statement: &mut S) -> Vec<&mut E> {
    match statement {
        S::Assert { condition, .. } => vec![condition],
        S::SliceSplit {
            slice, midpoint, ..
        } => vec![slice, midpoint],
        S::SharedArrayInitialize { source, .. } => vec![source],
        S::RangeInitialize { start, end, .. } => vec![start, end],
        S::ChunkInitialize { slice, size, .. } => vec![slice, size],
        S::Assign { value, .. } => vec![value],
        S::Initialize { fields, .. } => fields.iter_mut().collect(),
        S::SharedArrayMove { .. }
        | S::SharedArrayNext { .. }
        | S::EnumerateInitialize { .. }
        | S::EnumerateMove { .. }
        | S::EnumerateNext { .. }
        | S::RangeMove { .. }
        | S::RangeNext { .. }
        | S::ChunkMove { .. }
        | S::ChunkNext { .. }
        | S::Move { .. }
        | S::Copy { .. }
        | S::BeginStorage { .. }
        | S::EndStorage { .. }
        | S::Site { .. } => Vec::new(),
    }
}

/// The locals a statement names by a field rather than reads by an
/// expression.
fn statement_named_locals(statement: &S) -> Vec<&String> {
    match statement {
        S::SliceSplit { left, right, .. } => vec![left, right],
        S::SharedArrayInitialize { target, .. }
        | S::EnumerateInitialize { target, .. }
        | S::RangeInitialize { target, .. }
        | S::ChunkInitialize { target, .. }
        | S::Initialize { target, .. } => vec![target],
        S::SharedArrayMove { target, source }
        | S::EnumerateMove { target, source }
        | S::RangeMove { target, source }
        | S::ChunkMove { target, source }
        | S::Move { target, source, .. }
        | S::Copy { target, source, .. } => vec![target, source],
        S::SharedArrayNext { iterator, option }
        | S::EnumerateNext { iterator, option }
        | S::RangeNext {
            iterator, option, ..
        }
        | S::ChunkNext { iterator, option } => vec![iterator, option],
        S::Assert { .. }
        | S::Assign { .. }
        | S::BeginStorage { .. }
        | S::EndStorage { .. }
        | S::Site { .. } => Vec::new(),
    }
}

fn terminator_expressions_mut(terminator: &mut T) -> Vec<&mut E> {
    match terminator {
        T::If { condition, .. } => vec![condition],
        T::Call { arguments, .. } => arguments.iter_mut().collect(),
        T::Switch { scrutinee, .. } => vec![scrutinee],
        T::Goto { .. }
        | T::Drop { .. }
        | T::Return
        | T::Unreachable
        | T::Panic { .. }
        | T::BoxNew { .. }
        | T::BoxFree { .. } => Vec::new(),
    }
}

fn terminator_named_locals(terminator: &T) -> Vec<&String> {
    match terminator {
        T::Drop { local, .. } | T::BoxFree { local, .. } => vec![local],
        // A call's destination is counted apart, by `call_destination`.
        T::Call {
            function,
            owned_arguments,
            ..
        } => {
            let mut named = vec![function];
            named.extend(owned_arguments.iter().map(|argument| &argument.local));
            named
        }
        T::BoxNew {
            source,
            destination,
            ..
        } => vec![source, destination],
        T::If { .. }
        | T::Switch { .. }
        | T::Goto { .. }
        | T::Return
        | T::Unreachable
        | T::Panic { .. } => Vec::new(),
    }
}

fn statement_uses(
    statement: &S,
    reads: &mut BTreeMap<String, usize>,
    named: &mut BTreeSet<String>,
) {
    let mut statement = statement.clone();
    if let S::Assign { target, .. } = &statement {
        target_uses(target, reads, named);
    }
    for expression in statement_expressions_mut(&mut statement) {
        expression_uses(expression, reads, named);
    }
    named.extend(statement_named_locals(&statement).into_iter().cloned());
}

/// The locals an assignment's target place reads: the reference a `*r`
/// target writes through and an index; a local written in part, through a
/// field, is named rather than read, so it never moves.
fn target_uses(target: &E, reads: &mut BTreeMap<String, usize>, named: &mut BTreeSet<String>) {
    match target {
        E::Local { .. } => {}
        E::Field { base, .. } | E::EnumField { base, .. } => match base.as_ref() {
            E::Local { name } => {
                named.insert(name.clone());
            }
            base => target_uses(base, reads, named),
        },
        E::Deref { reference, .. } => expression_uses(reference, reads, named),
        E::Index { slice, index } => {
            target_uses(slice, reads, named);
            expression_uses(index, reads, named);
        }
        target => expression_uses(target, reads, named),
    }
}

/// Substitutes pending values into the reads an assignment's target makes:
/// an index is prepared, the reference a `*r` target writes through is not.
fn substitute_target(target: &mut E, pending: &mut Pending) {
    match target {
        E::Local { .. } => {}
        E::Field { base, .. } | E::EnumField { base, .. } => substitute_target(base, pending),
        E::Deref { reference, .. } => substitute(reference, pending, false),
        E::Index { slice, index } => {
            substitute_target(slice, pending);
            substitute(index, pending, true);
        }
        target => substitute(target, pending, false),
    }
}

fn terminator_uses(
    terminator: &T,
    reads: &mut BTreeMap<String, usize>,
    named: &mut BTreeSet<String>,
) {
    // A `match` on an enum splits a proof by its scrutinee's variants, and
    // that split names a local; the scrutinee stays one.
    if let T::Switch {
        scrutinee: E::Local { name },
        cases,
        ..
    } = terminator
        && cases.iter().any(|case| {
            matches!(
                case.label,
                crate::languages::rust::schema::SwitchLabel::Variant { .. }
            )
        })
    {
        named.insert(name.clone());
    }
    let mut terminator = terminator.clone();
    for expression in terminator_expressions_mut(&mut terminator) {
        expression_uses(expression, reads, named);
    }
    named.extend(terminator_named_locals(&terminator).into_iter().cloned());
}

/// The locals `expression` reads, and those it names by a field.
fn expression_uses(
    expression: &E,
    reads: &mut BTreeMap<String, usize>,
    named: &mut BTreeSet<String>,
) {
    match expression {
        E::Local { name } => *reads.entry(name.clone()).or_default() += 1,
        E::SharedArrayHasNext { iterator }
        | E::RangeHasNext { iterator }
        | E::ChunkHasNext { iterator }
        | E::ChunkRemainder { iterator } => {
            named.insert(iterator.clone());
        }
        E::EnumerateOptionIndex { option }
        | E::SharedArrayOptionElement { option }
        | E::SharedArrayOptionTag { option }
        | E::ChunkOptionSlice { option }
        | E::ChunkOptionTag { option } => {
            named.insert(option.clone());
        }
        E::Call {
            function,
            arguments,
        } => {
            named.insert(function.clone());
            for argument in arguments {
                expression_uses(argument, reads, named);
            }
        }
        E::Borrow { place, .. } => place_uses(place, reads, named),
        E::Field { base, .. } | E::EnumField { base, .. } => place_uses(base, reads, named),
        E::Index { slice, index } => {
            place_uses(slice, reads, named);
            expression_uses(index, reads, named);
        }
        _ => {
            for child in children(expression) {
                expression_uses(child, reads, named);
            }
        }
    }
}

/// The locals a place reads. A local that roots a place, as in `&x`, `x.f`
/// or `x[i]`, is the place's storage rather than a value, so it is named and
/// never moves; the reference a `*r` place goes through and an index are
/// read.
fn place_uses(place: &E, reads: &mut BTreeMap<String, usize>, named: &mut BTreeSet<String>) {
    match place {
        E::Local { name } => {
            named.insert(name.clone());
        }
        E::Field { base, .. } | E::EnumField { base, .. } => place_uses(base, reads, named),
        E::Index { slice, index } => {
            place_uses(slice, reads, named);
            expression_uses(index, reads, named);
        }
        place => expression_uses(place, reads, named),
    }
}

/// The sub-expressions `expression` evaluates.
fn children(expression: &E) -> Vec<&E> {
    match expression {
        E::IntegerFrom { value, .. }
        | E::Not { value }
        | E::BitwiseNot { value, .. }
        | E::Cast { value, .. }
        | E::Repeat { value, .. } => vec![value],
        E::ArrayToSlice { array, .. } => vec![array],
        E::Array { elements } => elements.iter().collect(),
        E::SliceLength { slice } => vec![slice],
        E::Index { slice, index } => vec![slice, index],
        E::Binary { left, right, .. } => vec![left, right],
        E::Borrow { place, .. } => vec![place],
        E::Deref { reference, .. } => vec![reference],
        E::Field { base, .. } | E::EnumField { base, .. } => vec![base],
        E::Call { arguments, .. } => arguments.iter().collect(),
        E::EnumConstruct { fields, .. } => fields.iter().collect(),
        E::ClosureInstance { captures, .. } => captures.iter().collect(),
        E::Integer { .. }
        | E::UnsignedInteger { .. }
        | E::SignedInteger { .. }
        | E::UsizeInteger { .. }
        | E::Boolean { .. }
        | E::NoneBox
        | E::Local { .. }
        | E::FunctionAddress { .. }
        | E::SharedArrayHasNext { .. }
        | E::EnumerateOptionIndex { .. }
        | E::RangeHasNext { .. }
        | E::SharedArrayOptionElement { .. }
        | E::SharedArrayOptionTag { .. }
        | E::ChunkHasNext { .. }
        | E::ChunkOptionSlice { .. }
        | E::ChunkOptionTag { .. }
        | E::ChunkRemainder { .. }
        | E::CallResult { .. } => Vec::new(),
    }
}

fn children_mut(expression: &mut E) -> Vec<&mut E> {
    match expression {
        E::IntegerFrom { value, .. }
        | E::Not { value }
        | E::BitwiseNot { value, .. }
        | E::Cast { value, .. }
        | E::Repeat { value, .. } => vec![value],
        E::ArrayToSlice { array, .. } => vec![array],
        E::Array { elements } => elements.iter_mut().collect(),
        E::SliceLength { slice } => vec![slice],
        E::Index { slice, index } => vec![slice, index],
        E::Binary { left, right, .. } => vec![left, right],
        E::Borrow { place, .. } => vec![place],
        E::Deref { reference, .. } => vec![reference],
        E::Field { base, .. } | E::EnumField { base, .. } => vec![base],
        E::Call { arguments, .. } => arguments.iter_mut().collect(),
        E::EnumConstruct { fields, .. } => fields.iter_mut().collect(),
        E::ClosureInstance { captures, .. } => captures.iter_mut().collect(),
        _ => Vec::new(),
    }
}

/// The pending values of a block, and those a read refused, whose
/// definitions go back just before the statement that reads them.
struct Pending<'a> {
    values: &'a mut BTreeMap<String, E>,
    refused: Vec<(String, E)>,
}

/// Whether `value` holds an operator whose panic the lowering checks:
/// arithmetic that can overflow, divide by zero, or shift too far.
fn checked(value: &E) -> bool {
    match value {
        E::Binary { operator, .. }
            if matches!(
                operator.as_str(),
                "add" | "sub" | "mul" | "div" | "rem" | "shl" | "shr"
            ) =>
        {
            true
        }
        value => children(value).into_iter().any(checked),
    }
}

/// Replaces each read of a pending value with the value, taking it out of
/// the pending values: it has its one read. A `prepared` read is one whose
/// lowering emits the checks of the operators it holds: an assignment's
/// value, an assertion, a call argument, an index, and the operands of an
/// operator or conversion there. A value with a checked operator moves only
/// into a prepared read; at any other read, as a constructor's field or a
/// branch condition, it stays a local.
fn substitute(expression: &mut E, pending: &mut Pending, prepared: bool) {
    if let E::Local { name } = expression
        && let Some(value) = pending.values.remove(name.as_str())
    {
        if prepared || !checked(&value) {
            *expression = value;
        } else {
            pending.refused.push((name.clone(), value));
        }
        return;
    }
    let operands = matches!(
        expression,
        E::Binary { .. }
            | E::Not { .. }
            | E::BitwiseNot { .. }
            | E::Cast { .. }
            | E::IntegerFrom { .. }
    );
    for child in children_mut(expression) {
        substitute(child, pending, prepared && operands);
    }
}

/// Substitutes into `statement`, and returns the definitions its reads
/// refused.
fn substitute_statement(statement: &mut S, values: &mut BTreeMap<String, E>) -> Vec<(String, E)> {
    if values.is_empty() {
        return Vec::new();
    }
    let mut pending = Pending {
        values,
        refused: Vec::new(),
    };
    let prepared = matches!(
        statement,
        S::Assign { .. } | S::Assert { .. } | S::Initialize { .. }
    );
    for expression in statement_expressions_mut(statement) {
        substitute(expression, &mut pending, prepared);
    }
    if let S::Assign { target, .. } = statement {
        substitute_target(target, &mut pending);
    }
    pending.refused
}

/// Substitutes into `terminator`, and returns the definitions its reads
/// refused. Call arguments are prepared; a branch condition and a `match`
/// scrutinee are not.
fn substitute_terminator(terminator: &mut T, values: &mut BTreeMap<String, E>) -> Vec<(String, E)> {
    if values.is_empty() {
        return Vec::new();
    }
    let mut pending = Pending {
        values,
        refused: Vec::new(),
    };
    let prepared = matches!(terminator, T::Call { .. });
    for expression in terminator_expressions_mut(terminator) {
        substitute(expression, &mut pending, prepared);
    }
    pending.refused
}

#[cfg(test)]
mod tests {
    use super::super::super::schema::{
        Expression as E, MirBlock, MirStatement as S, MirTerminator as T, Place, Span, SwitchCase,
        SwitchLabel, Type,
    };
    use std::collections::BTreeSet;

    fn local(name: &str) -> E {
        E::Local { name: name.into() }
    }
    fn assign(target: &str, value: E) -> S {
        S::Assign {
            target: local(target),
            value,
        }
    }
    fn binary(operator: &str, left: E, right: E) -> E {
        E::Binary {
            operator: operator.into(),
            left_type: Type::U32,
            right_type: Type::U32,
            left: Box::new(left),
            right: Box::new(right),
        }
    }
    fn place(name: &str) -> Place {
        Place {
            name: name.into(),
            value_type: Type::U32,
            span: Span { line: 1, column: 1 },
        }
    }
    /// Runs the pass over one block with temporaries `t1` and `t2`.
    fn substituted(statements: Vec<S>, terminator: T) -> (Vec<String>, MirBlock) {
        let mut locals = ["a", "b", "x", "t1", "t2"].map(place).to_vec();
        let mut blocks = vec![MirBlock {
            terminator_site: None,
            statements,
            terminator,
        }];
        let temporaries = BTreeSet::from(["t1".to_string(), "t2".to_string()]);
        super::substitute_pure_values(&mut locals, &mut blocks, &temporaries);
        let names = locals.into_iter().map(|local| local.name).collect();
        (names, blocks.pop().unwrap())
    }

    #[test]
    fn a_nested_operand_is_its_expression_again() {
        // `t1 = b * 2; x = a + t1;` is `x = a + b * 2`.
        let (locals, block) = substituted(
            vec![
                assign(
                    "t1",
                    binary(
                        "mul",
                        local("b"),
                        E::UnsignedInteger {
                            value: 2,
                            value_type: Type::U32,
                        },
                    ),
                ),
                assign("x", binary("add", local("a"), local("t1"))),
            ],
            T::Return,
        );
        assert_eq!(locals, ["a", "b", "x", "t2"]);
        assert!(matches!(
            block.statements.as_slice(),
            [S::Assign { value: E::Binary { operator, right, .. }, .. }]
                if operator == "add" && matches!(right.as_ref(), E::Binary { .. })
        ));
    }

    #[test]
    fn a_checked_value_does_not_move_where_its_check_would_be_lost() {
        // `Some(a + 1)` keeps `a + 1` in its temporary: the lowering checks
        // the overflow of a constructor's field nowhere.
        let some = E::EnumConstruct {
            name: "Option".into(),
            variant: "Some".into(),
            fields: vec![local("t1")],
        };
        let (locals, block) = substituted(
            vec![
                assign("t1", binary("add", local("a"), local("b"))),
                assign("x", some),
            ],
            T::Return,
        );
        assert!(locals.contains(&"t1".to_string()));
        assert!(matches!(
            block.statements.as_slice(),
            [S::Assign { target: E::Local { name }, .. }, _] if name == "t1"
        ));
    }

    #[test]
    fn a_call_result_read_once_in_its_successor_is_a_call_step() {
        // `t1 = f(a) -> bb1; bb1: x = t1 + 1` reads the call's result as a
        // step, and `t1` is gone.
        let mut locals = ["a", "x", "t1"].map(place).to_vec();
        let mut blocks = vec![
            MirBlock {
                terminator_site: None,
                statements: Vec::new(),
                terminator: T::Call {
                    function: "f".into(),
                    arguments: vec![local("a")],
                    owned_arguments: Vec::new(),
                    destination: "t1".into(),
                    target: 1,
                    through_pointer: false,
                    result: None,
                },
            },
            MirBlock {
                terminator_site: None,
                statements: vec![assign("x", binary("add", local("t1"), local("a")))],
                terminator: T::Return,
            },
        ];
        let temporaries = BTreeSet::from(["t1".to_string()]);
        super::call_steps(&mut locals, &mut blocks, &temporaries);
        assert!(locals.iter().all(|local| local.name != "t1"));
        assert!(matches!(
            blocks[0].terminator,
            T::Call {
                result: Some(0),
                ..
            }
        ));
        assert!(matches!(
            blocks[1].statements.as_slice(),
            [S::Assign { value: E::Binary { left, .. }, .. }]
                if matches!(left.as_ref(), E::CallResult { call: 0, function } if function == "f")
        ));
    }

    #[test]
    fn a_borrowed_local_and_an_enum_scrutinee_stay() {
        let (locals, _) = substituted(
            vec![
                assign("t1", binary("rem", local("a"), local("b"))),
                assign(
                    "x",
                    E::Borrow {
                        place: Box::new(local("t1")),
                        value_type: Type::U32,
                    },
                ),
                assign("t2", local("b")),
            ],
            T::Switch {
                scrutinee: local("t2"),
                cases: vec![SwitchCase {
                    label: SwitchLabel::Variant {
                        name: "None".into(),
                    },
                    target: 0,
                }],
                otherwise: None,
            },
        );
        assert!(locals.contains(&"t1".to_string()));
        assert!(locals.contains(&"t2".to_string()));
    }
}
