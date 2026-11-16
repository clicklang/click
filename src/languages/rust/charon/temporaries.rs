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
//! - assigned a call or a slice, or a borrow its one read does not take
//!   whole.
//!
//! A borrow moves into the read that takes it whole: an argument of its
//! block's call, `f(&mut x)`, a local's whole value, `let r = &mut x`, or a
//! reborrow, `&mut *t`, which is the borrow itself. A borrow of a place
//! rooted at a local, `x` or `x.f`, also moves past a statement that does
//! not name that local, since the place's address is unchanged.

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
        // A borrow is the value its one read takes whole: an argument of the
        // block's call, `f(&mut x)`, whose loan lasts the call, or a local's
        // whole value, `let r = &mut x`.
        let mut borrow_readers = match &block.terminator {
            T::Call { arguments, .. } => arguments
                .iter()
                .filter_map(|argument| match argument {
                    E::Local { name } => Some(name.clone()),
                    _ => None,
                })
                .collect::<BTreeSet<_>>(),
            _ => BTreeSet::new(),
        };
        borrow_readers.extend(
            block
                .statements
                .iter()
                .filter_map(|statement| match statement {
                    S::Assign {
                        target: E::Local { .. },
                        value: E::Local { name },
                    } => Some(name.clone()),
                    // A reborrow, `&mut *t`, of a borrow `t = &mut x` is
                    // `&mut x`.
                    S::Assign {
                        value: E::Borrow { place, .. },
                        ..
                    } => match place.as_ref() {
                        E::Deref { reference, .. } => match reference.as_ref() {
                            E::Local { name } => Some(name.clone()),
                            _ => None,
                        },
                        _ => None,
                    },
                    _ => None,
                }),
        );
        // The pending borrows of a place rooted at a local, by that local:
        // the place's address is the same until a statement names the local.
        let mut rooted = BTreeMap::<String, String>::new();
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
                } if substitutable(name)
                    && (pure(value)
                        || (matches!(value, E::Borrow { place, .. } if pure(place))
                            && borrow_readers.contains(name))) =>
                {
                    if let E::Borrow { place, .. } = value
                        && let Some(root) = place_root(place)
                    {
                        rooted.insert(name.clone(), root.clone());
                    }
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
                    // storage markers, checks and other pure definitions. A
                    // borrow of a place rooted at a local the statement does
                    // not name moves past it: its address is unchanged.
                    let mentioned = mentioned_locals(&statement);
                    for (name, value) in std::mem::take(&mut pending) {
                        if rooted
                            .get(&name)
                            .is_some_and(|root| !mentioned.contains(root))
                        {
                            pending.insert(name, value);
                            continue;
                        }
                        rooted.remove(&name);
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

/// The kind of iterator an iterator statement builds or moves.
#[derive(Clone, Copy, PartialEq, Eq)]
enum IteratorKind {
    SharedArray,
    Enumerate,
    Range,
    Chunk,
}

/// The iterator `statement` builds, as its kind and the local it builds.
fn iterator_definition(statement: &mut S) -> Option<(IteratorKind, &mut String)> {
    match statement {
        S::SharedArrayInitialize { target, .. } | S::SharedArrayMove { target, .. } => {
            Some((IteratorKind::SharedArray, target))
        }
        S::EnumerateInitialize { target, .. } | S::EnumerateMove { target, .. } => {
            Some((IteratorKind::Enumerate, target))
        }
        S::RangeInitialize { target, .. } | S::RangeMove { target, .. } => {
            Some((IteratorKind::Range, target))
        }
        S::ChunkInitialize { target, .. } | S::ChunkMove { target, .. } => {
            Some((IteratorKind::Chunk, target))
        }
        _ => None,
    }
}

/// The iterator `statement` moves: its kind, the local it moves into, and
/// the local it moves from.
/// Binds a range loop's variable where `next` yields it. Once the iterator
/// protocol has split a range's `next` into its two outcomes, the `Option`
/// it returns is read only by the `match` the split replaced and by the
/// `Some` arm's first statement, `i = (opt as Some).0`. That statement
/// becomes the yielding outcome's own binding, `i = iter.start`, neither
/// outcome builds the `Option`, and its temporary is gone.
pub(super) fn bind_range_payloads(
    locals: &mut Vec<Place>,
    blocks: &mut [MirBlock],
    temporaries: &BTreeSet<String>,
) {
    let mut mentions = BTreeMap::<String, usize>::new();
    for block in blocks.iter() {
        for statement in &block.statements {
            if matches!(statement, S::BeginStorage { .. } | S::EndStorage { .. }) {
                continue;
            }
            for name in mentioned_locals(statement) {
                *mentions.entry(name).or_default() += 1;
            }
        }
        let mut reads = BTreeMap::new();
        let mut named = BTreeSet::new();
        terminator_uses(&block.terminator, &mut reads, &mut named);
        if let Some(destination) = call_destination(&block.terminator) {
            named.insert(destination.clone());
        }
        named.extend(reads.into_keys());
        for name in named {
            *mentions.entry(name).or_default() += 1;
        }
    }
    let transparent = |statement: &S| {
        matches!(
            statement,
            S::BeginStorage { .. } | S::EndStorage { .. } | S::Site { .. }
        )
    };
    let mut removed = BTreeSet::new();
    for index in 0..blocks.len() {
        let (option, target) = match (blocks[index].statements.last(), &blocks[index].terminator) {
            (
                Some(S::RangeNext {
                    option: Some(option),
                    payload: None,
                    taken: Some(true),
                    ..
                }),
                T::Goto { target },
            ) => (option.clone(), *target),
            _ => continue,
        };
        // The replaced `match`, the two outcomes and the binding: nothing
        // else names the `Option`.
        if !temporaries.contains(&option) || mentions.get(&option) != Some(&4) {
            continue;
        }
        let Some(position) = blocks[target]
            .statements
            .iter()
            .position(|statement| !transparent(statement))
        else {
            continue;
        };
        let S::Assign {
            target: E::Local { name: payload },
            value:
                E::EnumField {
                    base,
                    variant,
                    index: 0,
                    ..
                },
        } = &blocks[target].statements[position]
        else {
            continue;
        };
        if variant != "Some" || !matches!(base.as_ref(), E::Local { name } if *name == option) {
            continue;
        }
        let payload = payload.clone();
        blocks[target].statements.remove(position);
        for block in blocks.iter_mut() {
            for statement in &mut block.statements {
                if let S::RangeNext {
                    option: next_option,
                    payload: next_payload,
                    taken,
                    ..
                } = statement
                    && next_option.as_deref() == Some(option.as_str())
                {
                    *next_option = None;
                    if *taken == Some(true) {
                        *next_payload = Some(payload.clone());
                    }
                }
            }
            // The `match` the protocol replaced, which no block reaches.
            if matches!(&block.terminator, T::Switch { scrutinee: E::Local { name }, .. } if *name == option)
            {
                block.terminator = T::Unreachable;
            }
        }
        removed.insert(option);
    }
    if removed.is_empty() {
        return;
    }
    for block in blocks.iter_mut() {
        block.statements.retain(|statement| match statement {
            S::BeginStorage { local } | S::EndStorage { local } => !removed.contains(local),
            _ => true,
        });
    }
    locals.retain(|local| !removed.contains(&local.name));
}

fn iterator_move(statement: &S) -> Option<(IteratorKind, &String, &String)> {
    match statement {
        S::SharedArrayMove { target, source } => Some((IteratorKind::SharedArray, target, source)),
        S::EnumerateMove { target, source } => Some((IteratorKind::Enumerate, target, source)),
        S::RangeMove { target, source } => Some((IteratorKind::Range, target, source)),
        S::ChunkMove { target, source } => Some((IteratorKind::Chunk, target, source)),
        _ => None,
    }
}

/// Builds each range iterator in the local the program moves it into. MIR builds
/// a `for` loop's iterator in a temporary and moves it, sometimes twice,
/// into the loop's own: `t1 = 0..n; t2 = t1; iter = t2` is `iter = 0..n`.
/// A move from a temporary that nothing else names, whose definition comes
/// just before it, past nothing but storage markers and source sites, takes
/// that definition's place, and the temporary is gone. The definition may
/// end a block that only jumps to the move's.
pub(super) fn collapse_iterator_moves(
    locals: &mut Vec<Place>,
    blocks: &mut [MirBlock],
    temporaries: &BTreeSet<String>,
) {
    let mut mentions = BTreeMap::<String, usize>::new();
    let mut predecessors = vec![0usize; blocks.len()];
    for block in blocks.iter() {
        for statement in &block.statements {
            if matches!(statement, S::BeginStorage { .. } | S::EndStorage { .. }) {
                continue;
            }
            let mut named = mentioned_locals(statement);
            if let S::EnumerateInitialize { source, .. } = statement {
                named.insert(source.clone());
            }
            for name in named {
                *mentions.entry(name).or_default() += 1;
            }
        }
        let mut reads = BTreeMap::new();
        let mut named = BTreeSet::new();
        terminator_uses(&block.terminator, &mut reads, &mut named);
        if let Some(destination) = call_destination(&block.terminator) {
            named.insert(destination.clone());
        }
        for name in named.into_iter().chain(reads.into_keys()) {
            *mentions.entry(name).or_default() += 1;
        }
        for target in successors(&block.terminator) {
            if let Some(count) = predecessors.get_mut(target) {
                *count += 1;
            }
        }
    }
    // The block that only jumps to `block`, when `block` has no other way in.
    let jumped_from = |blocks: &[MirBlock], block: usize| {
        if predecessors.get(block) != Some(&1) {
            return None;
        }
        blocks
            .iter()
            .position(|other| matches!(other.terminator, T::Goto { target } if target == block))
    };
    let transparent = |statement: &S| {
        matches!(
            statement,
            S::BeginStorage { .. } | S::EndStorage { .. } | S::Site { .. }
        )
    };
    let mut removed = BTreeSet::new();
    for block in 0..blocks.len() {
        let mut index = 0;
        while index < blocks[block].statements.len() {
            let Some((kind, target, source)) = iterator_move(&blocks[block].statements[index])
            else {
                index += 1;
                continue;
            };
            let (target, source) = (target.clone(), source.clone());
            // A slice or chunk iterator's moves also pass its liveness flag,
            // which the lowering keeps per local; only a range moves as a
            // plain value.
            if kind != IteratorKind::Range
                || !temporaries.contains(&source)
                || mentions.get(&source) != Some(&2)
            {
                index += 1;
                continue;
            }
            // The definition, found walking back past transparent statements,
            // across a block that only jumps here.
            let mut at = (block, index);
            let definition = loop {
                let (here, position) = at;
                match position.checked_sub(1) {
                    Some(previous) => {
                        let statement = &blocks[here].statements[previous];
                        if transparent(statement) {
                            at = (here, previous);
                            continue;
                        }
                        break Some((here, previous));
                    }
                    None => match jumped_from(blocks, here) {
                        Some(from) if from != here => {
                            at = (from, blocks[from].statements.len());
                        }
                        _ => break None,
                    },
                }
            };
            let Some((from, position)) = definition else {
                index += 1;
                continue;
            };
            let defines = matches!(
                iterator_definition(&mut blocks[from].statements[position]),
                Some((defined, local)) if defined == kind && *local == source
            );
            if !defines {
                index += 1;
                continue;
            }
            let mut statement = blocks[from].statements.remove(position);
            if let Some((_, local)) = iterator_definition(&mut statement) {
                *local = target;
            }
            if from == block {
                index -= 1;
            }
            blocks[block].statements[index] = statement;
            mentions.insert(source.clone(), 0);
            removed.insert(source);
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
        // A read of an element: the lowering checks its index where it
        // prepares the read (`checked`).
        E::Index { slice, index } => pure(slice) && pure(index),
        // A call has effects; a borrow begins a loan; a slice and the
        // iterator protocol need their own preparation.
        E::Call { .. }
        | E::Borrow { .. }
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
        | S::ChunkNext { iterator, option } => vec![iterator, option],
        S::RangeNext {
            iterator,
            option,
            payload,
            ..
        } => std::iter::once(iterator)
            .chain(option)
            .chain(payload)
            .collect(),
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

/// The local a place of fields is rooted at, `x` of `x.f.g`; `None` for a
/// place through a reference or an index, whose address a statement can
/// change.
fn place_root(place: &E) -> Option<&String> {
    match place {
        E::Local { name } => Some(name),
        E::Field { base, .. } => place_root(base),
        _ => None,
    }
}

/// Every local `statement` names: those it reads, assigns, or names by a
/// field.
fn mentioned_locals(statement: &S) -> BTreeSet<String> {
    let mut reads = BTreeMap::new();
    let mut named = BTreeSet::new();
    statement_uses(statement, &mut reads, &mut named);
    named.extend(reads.into_keys());
    if let S::Assign { target, .. } = statement
        && let Some(root) = place_root(target)
    {
        named.insert(root.clone());
    }
    named
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

/// Whether `value` holds an operation whose panic the lowering checks:
/// arithmetic that can overflow, divide by zero, or shift too far, and an
/// index that can be out of bounds.
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
        E::Index { .. } => true,
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
    // The place a borrow names, read through it: `*(&mut x)` is `x`.
    if let E::Deref { reference, .. } = expression
        && let E::Borrow { place, .. } = reference.as_mut()
    {
        let place = std::mem::replace(place.as_mut(), E::Boolean { value: false });
        *expression = place;
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
    fn an_indexed_read_moves_only_where_its_bounds_check_is_emitted() {
        let read = || E::Index {
            slice: Box::new(local("a")),
            index: Box::new(local("b")),
        };
        // `t1 = a[b]; x = t1 + 1` is `x = a[b] + 1`.
        let (locals, _) = substituted(
            vec![
                assign("t1", read()),
                assign("x", binary("add", local("t1"), local("b"))),
            ],
            T::Return,
        );
        assert!(!locals.contains(&"t1".to_string()));
        // A constructor's field checks no index, so `a[b]` stays in `t1`.
        let (locals, _) = substituted(
            vec![
                assign("t1", read()),
                assign(
                    "x",
                    E::EnumConstruct {
                        name: "Option".into(),
                        variant: "Some".into(),
                        fields: vec![local("t1")],
                    },
                ),
            ],
            T::Return,
        );
        assert!(locals.contains(&"t1".to_string()));
    }

    #[test]
    fn a_borrow_the_block_s_call_takes_is_that_argument() {
        // `t1 = &mut a; f(t1)` is `f(&mut a)`.
        let mut locals = ["a", "t1"].map(place).to_vec();
        let borrow = E::Borrow {
            place: Box::new(local("a")),
            value_type: Type::U32,
        };
        let mut blocks = vec![MirBlock {
            statements: vec![assign("t1", borrow)],
            terminator: T::Call {
                function: "f".into(),
                arguments: vec![local("t1")],
                owned_arguments: Vec::new(),
                destination: "unit".into(),
                target: 0,
                through_pointer: false,
                result: None,
            },
            terminator_site: None,
        }];
        let temporaries = BTreeSet::from(["t1".to_string()]);
        super::substitute_pure_values(&mut locals, &mut blocks, &temporaries);
        assert!(locals.iter().all(|local| local.name != "t1"));
        assert!(blocks[0].statements.is_empty());
        assert!(matches!(
            &blocks[0].terminator,
            T::Call { arguments, .. } if matches!(arguments.as_slice(), [E::Borrow { .. }])
        ));
    }

    fn call(arguments: Vec<E>) -> T {
        T::Call {
            function: "f".into(),
            arguments,
            owned_arguments: Vec::new(),
            destination: "unit".into(),
            target: 0,
            through_pointer: false,
            result: None,
        }
    }

    fn borrow(place: E) -> E {
        E::Borrow {
            place: Box::new(place),
            value_type: Type::U32,
        }
    }

    #[test]
    fn a_reborrowed_borrow_is_the_borrow_and_passes_unrelated_statements() {
        // `t1 = &mut a; t2 = &mut *t1; x = b; f(t2)` is `x = b; f(&mut a)`:
        // the reborrow of a borrow is the borrow, and `x = b` names no local
        // the borrowed place is rooted at.
        let (locals, block) = substituted(
            vec![
                assign("t1", borrow(local("a"))),
                assign(
                    "t2",
                    borrow(E::Deref {
                        reference: Box::new(local("t1")),
                        value_type: Type::U32,
                    }),
                ),
                assign("x", local("b")),
            ],
            call(vec![local("t2")]),
        );
        assert_eq!(locals, ["a", "b", "x"]);
        assert!(matches!(block.statements.as_slice(), [S::Assign { .. }]));
        assert!(matches!(
            &block.terminator,
            T::Call { arguments, .. } if matches!(
                arguments.as_slice(),
                [E::Borrow { place, .. }] if matches!(place.as_ref(), E::Local { name } if name == "a")
            )
        ));
    }

    #[test]
    fn a_borrow_does_not_pass_a_statement_naming_its_place() {
        // `x = a` reads `a`, so `t1 = &mut a` stays before it.
        let (locals, _) = substituted(
            vec![assign("t1", borrow(local("a"))), assign("x", local("a"))],
            call(vec![local("t1")]),
        );
        assert!(locals.contains(&"t1".to_string()));
    }

    #[test]
    fn a_borrow_a_named_local_takes_whole_is_its_value() {
        // `t1 = &mut a; x = t1` is `x = &mut a`.
        let (locals, block) = substituted(
            vec![assign("t1", borrow(local("a"))), assign("x", local("t1"))],
            T::Return,
        );
        assert!(!locals.contains(&"t1".to_string()));
        assert!(matches!(
            block.statements.as_slice(),
            [S::Assign {
                value: E::Borrow { .. },
                ..
            }]
        ));
    }

    #[test]
    fn a_range_is_built_in_the_local_it_is_moved_into() {
        // `t1 = 0..a; t2 = t1; goto; b = t2` is `b = 0..a`, built where the
        // last move was.
        let mut locals = ["a", "b", "t1", "t2"].map(place).to_vec();
        let mut blocks = vec![
            MirBlock {
                statements: vec![
                    S::RangeInitialize {
                        target: "t1".into(),
                        start: E::UnsignedInteger {
                            value: 0,
                            value_type: Type::U32,
                        },
                        end: local("a"),
                    },
                    S::RangeMove {
                        target: "t2".into(),
                        source: "t1".into(),
                    },
                ],
                terminator: T::Goto { target: 1 },
                terminator_site: None,
            },
            MirBlock {
                statements: vec![
                    S::EndStorage { local: "t1".into() },
                    S::RangeMove {
                        target: "b".into(),
                        source: "t2".into(),
                    },
                ],
                terminator: T::Return,
                terminator_site: None,
            },
        ];
        let temporaries = BTreeSet::from(["t1".to_string(), "t2".to_string()]);
        super::collapse_iterator_moves(&mut locals, &mut blocks, &temporaries);
        assert_eq!(
            locals
                .iter()
                .map(|local| local.name.as_str())
                .collect::<Vec<_>>(),
            ["a", "b"]
        );
        assert!(blocks[0].statements.is_empty());
        assert!(matches!(
            blocks[1].statements.as_slice(),
            [S::RangeInitialize { target, .. }] if target == "b"
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
