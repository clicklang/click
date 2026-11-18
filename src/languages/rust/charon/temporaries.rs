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

/// Puts each temporary that holds an unchanging value back where it is
/// read. A temporary of `temporaries` assigned once holds the same value at
/// every read, however many and in whichever block, when that value is a
/// literal, as `x[0] = x[0] * k` reads its index twice, a copy of a
/// parameter the body never writes, moves or borrows, as `t = x; ...; f(t)`
/// passes `x`, or a reference borrowing a place rooted at a local, as
/// `t = &mut w; f(t); g(t)` passes `&mut w` to both. Its assignment, storage
/// markers and local go.
pub(super) fn substitute_literals(
    locals: &mut Vec<Place>,
    blocks: &mut [MirBlock],
    temporaries: &BTreeSet<String>,
    parameters: &BTreeMap<String, super::super::schema::Type>,
) {
    let mut reads = BTreeMap::<String, usize>::new();
    let mut named = BTreeSet::<String>::new();
    let mut assignments = BTreeMap::<String, Vec<E>>::new();
    for block in blocks.iter() {
        for statement in &block.statements {
            statement_uses(statement, &mut reads, &mut named);
            if let S::Assign {
                target: E::Local { name },
                value,
            } = statement
            {
                assignments
                    .entry(name.clone())
                    .or_default()
                    .push(value.clone());
            }
        }
        terminator_uses(&block.terminator, &mut reads, &mut named);
        if let Some(destination) = call_destination(&block.terminator) {
            named.insert(destination.clone());
        }
    }
    let unchanged = unchanged_parameters(blocks, parameters);
    let types: BTreeMap<&String, &super::super::schema::Type> = locals
        .iter()
        .map(|local| (&local.name, &local.value_type))
        .chain(parameters.iter())
        .collect();
    // Each temporary assigned once, by its one value.
    let candidates: BTreeMap<String, E> = assignments
        .into_iter()
        .filter(|(name, values)| {
            temporaries.contains(name) && !named.contains(name) && values.len() == 1
        })
        .filter_map(|(name, mut values)| Some((name, values.pop()?)))
        .collect();
    // A candidate's value with the unchanging candidates it reads put back,
    // or `None` when it changes. A reborrow `t = &mut *u` of `u = &mut x` is
    // `&mut x`, so a chain of borrows resolves link by link, each once.
    let mut resolved = BTreeMap::<String, Option<E>>::new();
    let names: Vec<String> = candidates.keys().cloned().collect();
    for name in &names {
        resolve(
            name,
            &candidates,
            &unchanged,
            &types,
            &mut resolved,
            &mut BTreeSet::new(),
        );
    }
    let literals: BTreeMap<String, E> = resolved
        .into_iter()
        .filter_map(|(name, value)| Some((name, value?)))
        .collect();
    if literals.is_empty() {
        return;
    }
    for block in blocks.iter_mut() {
        block.statements.retain(|statement| match statement {
            S::Assign {
                target: E::Local { name },
                ..
            }
            | S::BeginStorage { local: name }
            | S::EndStorage { local: name } => !literals.contains_key(name),
            _ => true,
        });
        for statement in &mut block.statements {
            // A target reads its index and the reference it writes through;
            // a local it writes is no read.
            if let S::Assign { target, .. } = statement
                && !matches!(target, E::Local { .. })
            {
                put_back(target, &literals);
            }
            for expression in statement_expressions_mut(statement) {
                put_back(expression, &literals);
            }
        }
        for expression in terminator_expressions_mut(&mut block.terminator) {
            put_back(expression, &literals);
        }
    }
    locals.retain(|local| !literals.contains_key(&local.name));
}

/// Replaces each read of a local of `values` in `expression` with its value,
/// and `*&p` with `p`.
fn put_back(expression: &mut E, values: &BTreeMap<String, E>) {
    if let E::Local { name } = expression
        && let Some(value) = values.get(name)
    {
        *expression = value.clone();
        return;
    }
    for child in children_mut(expression) {
        put_back(child, values);
    }
    if let E::Deref { reference, .. } = expression
        && let E::Borrow { place, .. } = reference.as_mut()
    {
        *expression = std::mem::replace(place.as_mut(), E::NoneBox);
    }
    // A shared reborrow of a shared slice borrow is that borrow.
    if let E::Borrow {
        place,
        value_type: super::super::schema::Type::ByteSlice { mutable: false },
    } = expression
        && matches!(
            place.as_ref(),
            E::Borrow {
                value_type: super::super::schema::Type::ByteSlice { mutable: false },
                ..
            }
        )
    {
        *expression = std::mem::replace(place.as_mut(), E::NoneBox);
    }
}

/// The unchanging value of candidate `name`, memoized in `resolved`: its one
/// value with the unchanging candidates it reads put back, when that is a
/// literal, a copy of an `unchanged` parameter, or, for a reference, a borrow
/// of a place rooted at a local, whose address rustc keeps for the borrow's
/// life. A slice is a pointer and a length its readers take apart, so a
/// slice's borrow stays.
fn resolve(
    name: &str,
    candidates: &BTreeMap<String, E>,
    unchanged: &BTreeSet<String>,
    types: &BTreeMap<&String, &super::super::schema::Type>,
    resolved: &mut BTreeMap<String, Option<E>>,
    visiting: &mut BTreeSet<String>,
) -> Option<E> {
    if let Some(value) = resolved.get(name) {
        return value.clone();
    }
    let value = candidates.get(name)?;
    if !visiting.insert(name.to_string()) {
        return None;
    }
    // Every local the value reads, including a slice a length takes apart.
    fn locals_in(expression: &E, out: &mut BTreeSet<String>) {
        if let E::Local { name } = expression {
            out.insert(name.clone());
        }
        for child in children(expression) {
            locals_in(child, out);
        }
    }
    let mut reads = BTreeSet::new();
    locals_in(value, &mut reads);
    let mut inner = BTreeMap::new();
    for read in &reads {
        if let Some(read_value) = resolve(read, candidates, unchanged, types, resolved, visiting) {
            inner.insert(read.clone(), read_value);
        }
    }
    let mut value = value.clone();
    put_back(&mut value, &inner);
    visiting.remove(name);
    let unchanging = match &value {
        E::Borrow { place, value_type } => match types.get(&name.to_string()) {
            Some(super::super::schema::Type::Reference { .. }) => place_root(place).is_some(),
            // A shared slice borrow of a shared slice local: its pointer
            // and length never change while the borrow lives.
            Some(super::super::schema::Type::ByteSlice { mutable: false }) => {
                matches!(
                    value_type,
                    super::super::schema::Type::ByteSlice { mutable: false }
                ) && matches!(place.as_ref(), E::Local { name } if matches!(
                    types.get(name),
                    Some(super::super::schema::Type::ByteSlice { mutable: false })
                ))
            }
            _ => false,
        },
        value => unchanging_scalar(value, unchanged),
    };
    let result = unchanging.then_some(value);
    resolved.insert(name.to_string(), result.clone());
    result
}

/// Whether `value` is the same wherever it is read: a literal, an
/// `unchanged` parameter, or the length or a conversion of one.
fn unchanging_scalar(value: &E, unchanged: &BTreeSet<String>) -> bool {
    match value {
        E::Integer { .. }
        | E::UnsignedInteger { .. }
        | E::SignedInteger { .. }
        | E::UsizeInteger { .. }
        | E::Boolean { .. }
        | E::NoneBox => true,
        E::Local { name } => unchanged.contains(name),
        E::SliceLength { slice } => match slice.as_ref() {
            E::Borrow { place, .. } => unchanging_scalar(place, unchanged),
            slice => unchanging_scalar(slice, unchanged),
        },
        E::Cast { value, .. } | E::IntegerFrom { value, .. } => unchanging_scalar(value, unchanged),
        _ => false,
    }
}

/// The parameters the body never changes: none is assigned (other than
/// through a reference it holds), named by a statement or terminator field
/// (a move, a drop, an initialization), a call's destination, or borrowed,
/// apart from a shared borrow of a reference or slice.
fn unchanged_parameters(
    blocks: &[MirBlock],
    parameters: &BTreeMap<String, super::super::schema::Type>,
) -> BTreeSet<String> {
    // The local a target writes, unless it writes through a reference.
    fn written(target: &E) -> Option<&String> {
        match target {
            E::Local { name } => Some(name),
            E::Field { base, .. } | E::EnumField { base, .. } => written(base),
            E::Index { slice, .. } => written(slice),
            _ => None,
        }
    }
    // A shared borrow of a reference or a slice cannot change it: the
    // variable holds an address and a length, with no interior mutability.
    let pointer_like = |name: &String| {
        matches!(
            parameters.get(name),
            Some(
                super::super::schema::Type::Reference { .. }
                    | super::super::schema::Type::ByteSlice { .. }
                    | super::super::schema::Type::ScalarSlice { .. }
            )
        )
    };
    fn borrowed(
        expression: &E,
        out: &mut BTreeSet<String>,
        pointer_like: &dyn Fn(&String) -> bool,
    ) {
        if let E::Borrow { place, value_type } = expression
            && let Some(root) = written(place)
        {
            let shared = matches!(
                value_type,
                super::super::schema::Type::Reference { mutable: false, .. }
                    | super::super::schema::Type::ByteSlice { mutable: false }
                    | super::super::schema::Type::ScalarSlice { mutable: false, .. }
            );
            if !(shared && pointer_like(root)) {
                out.insert(root.clone());
            }
        }
        for child in children(expression) {
            borrowed(child, out, pointer_like);
        }
    }
    // What a statement or terminator names by a field (a move, an
    // initialization, a drop), the locals a target writes, and the locals
    // the body borrows other than by a shared borrow of a pointer.
    let mut changed = BTreeSet::new();
    for block in blocks {
        for statement in &block.statements {
            if let S::Assign { target, .. } = statement
                && let Some(root) = written(target)
            {
                changed.insert(root.clone());
            }
            changed.extend(statement_named_locals(statement).into_iter().cloned());
            let mut statement = statement.clone();
            for expression in statement_expressions_mut(&mut statement) {
                borrowed(expression, &mut changed, &pointer_like);
            }
        }
        changed.extend(
            terminator_named_locals(&block.terminator)
                .into_iter()
                .cloned(),
        );
        let mut terminator = block.terminator.clone();
        for expression in terminator_expressions_mut(&mut terminator) {
            borrowed(expression, &mut changed, &pointer_like);
        }
        if let T::Call { destination, .. } | T::BoxNew { destination, .. } = &block.terminator {
            changed.insert(destination.clone());
        }
    }
    parameters
        .keys()
        .filter(|name| !changed.contains(*name))
        .cloned()
        .collect()
}

/// Removes the temporaries of `temporaries` the body never uses: those no
/// statement or terminator names apart from their storage markers and their
/// writes of pure values, and a `()` temporary that is only a call's
/// destination, which the call never writes. Their storage markers and
/// writes go with them.
pub(super) fn remove_unused(
    locals: &mut Vec<Place>,
    blocks: &mut [MirBlock],
    temporaries: &BTreeSet<String>,
) {
    let mut used = BTreeSet::new();
    for block in blocks.iter() {
        for statement in &block.statements {
            match statement {
                S::BeginStorage { .. } | S::EndStorage { .. } => {}
                // Writing a pure value to a local no one reads uses only
                // what the value reads.
                S::Assign {
                    target: E::Local { .. },
                    value,
                } if pure(value) => {
                    let mut reads = BTreeMap::new();
                    let mut named = BTreeSet::new();
                    expression_uses(value, &mut reads, &mut named);
                    used.extend(reads.into_keys());
                    used.extend(named);
                }
                statement => used.extend(mentioned_locals(statement)),
            }
        }
        let mut reads = BTreeMap::new();
        let mut named = BTreeSet::new();
        terminator_uses(&block.terminator, &mut reads, &mut named);
        used.extend(reads.into_keys());
        used.extend(named);
        if let T::Call { destination, .. } = &block.terminator {
            used.insert(destination.clone());
        }
        if let T::BoxNew {
            source,
            destination,
            ..
        } = &block.terminator
        {
            used.insert(source.clone());
            used.insert(destination.clone());
        }
    }
    // A `()` call result holds nothing, so being a destination is no use.
    let unit: BTreeSet<&String> = locals
        .iter()
        .filter(|local| local.value_type == super::super::schema::Type::Unit)
        .map(|local| &local.name)
        .collect();
    let unused: BTreeSet<String> = locals
        .iter()
        .map(|local| &local.name)
        .filter(|name| temporaries.contains(*name))
        .filter(|name| {
            !used.contains(*name) || (unit.contains(name) && only_destination(blocks, name))
        })
        .cloned()
        .collect();
    if unused.is_empty() {
        return;
    }
    for block in blocks.iter_mut() {
        block.statements.retain(|statement| match statement {
            S::BeginStorage { local } | S::EndStorage { local } => !unused.contains(local),
            S::Assign {
                target: E::Local { name },
                ..
            } => !unused.contains(name),
            _ => true,
        });
    }
    locals.retain(|local| !unused.contains(&local.name));
}

/// Whether `name` is named only as a call's destination.
fn only_destination(blocks: &[MirBlock], name: &str) -> bool {
    blocks.iter().all(|block| {
        let statements = block.statements.iter().all(|statement| {
            matches!(statement, S::BeginStorage { .. } | S::EndStorage { .. })
                || !mentioned_locals(statement).contains(name)
        });
        let mut reads = BTreeMap::new();
        let mut named = BTreeSet::new();
        terminator_uses(&block.terminator, &mut reads, &mut named);
        statements && !reads.contains_key(name) && !named.contains(name)
    })
}

/// Returns the value MIR writes to the return place where nothing runs
/// between the write and the return, as `return value` does in C.
///
/// MIR always writes `_0` and then returns `_0`. When the function writes
/// `_0` once, and that write reaches `Return` past only source sites and
/// storage markers, through blocks entered from nowhere else, the return
/// returns the written value and `_0` is no longer a local:
///
/// - `_0 = value` ends its block in `ReturnValue { value }`;
/// - a call whose destination is `_0`, a tail call, becomes a call step,
///   and its successor ends in `ReturnValue` of the step's result.
///
/// A return place that cleanup follows, that is written more than once, or
/// that holds a value other than a scalar keeps its local.
pub(super) fn return_values(locals: &mut Vec<Place>, blocks: &mut [MirBlock], return_place: &str) {
    let Some(place) = locals.iter().find(|local| local.name == return_place) else {
        return;
    };
    if !returned_directly(&place.value_type) {
        return;
    }
    let transparent = |statement: &S| {
        matches!(
            statement,
            S::Site { .. } | S::BeginStorage { .. } | S::EndStorage { .. }
        )
    };
    // The one place that writes the return place: a statement, or a call.
    let mut write = None;
    for (index, block) in blocks.iter().enumerate() {
        let mut reads = BTreeMap::new();
        let mut named = BTreeSet::new();
        terminator_uses(&block.terminator, &mut reads, &mut named);
        if reads.contains_key(return_place) || named.contains(return_place) {
            return;
        }
        if call_destination(&block.terminator).is_some_and(|name| name == return_place) {
            if write.is_some() {
                return;
            }
            write = Some((index, None));
        }
        for (position, statement) in block.statements.iter().enumerate() {
            if transparent(statement)
                || !mentioned_locals(statement)
                    .iter()
                    .any(|name| name == return_place)
            {
                continue;
            }
            if write.is_some() {
                return;
            }
            write = Some((index, Some(position)));
        }
    }
    let Some((block, position)) = write else {
        return;
    };
    let mut predecessors = vec![0usize; blocks.len()];
    for candidate in blocks.iter() {
        for target in successors(&candidate.terminator) {
            if let Some(count) = predecessors.get_mut(target) {
                *count += 1;
            }
        }
    }
    // Whether the end of block `from` reaches `Return` past nothing else.
    let reaches_return = |from: usize| {
        let mut next = from;
        let mut visited = BTreeSet::new();
        loop {
            if !visited.insert(next) {
                return false;
            }
            match &blocks[next].terminator {
                T::Return => return true,
                T::Goto { target }
                    if predecessors.get(*target) == Some(&1)
                        && blocks[*target].statements.iter().all(transparent) =>
                {
                    next = *target;
                }
                _ => return false,
            }
        }
    };
    match position {
        Some(position) => {
            let S::Assign {
                target: E::Local { name },
                ..
            } = &blocks[block].statements[position]
            else {
                return;
            };
            if name != return_place
                || !blocks[block].statements[position + 1..]
                    .iter()
                    .all(transparent)
                || !reaches_return(block)
            {
                return;
            }
            let S::Assign { value, .. } = blocks[block].statements.remove(position) else {
                unreachable!("the return place's write is an assignment")
            };
            blocks[block].terminator = T::ReturnValue { value };
        }
        None => {
            let T::Call {
                function,
                target,
                through_pointer,
                ..
            } = &blocks[block].terminator
            else {
                unreachable!("the return place's writer is a call")
            };
            // A call through a pointer assigns its destination; it is no step.
            if *through_pointer {
                return;
            }
            let (function, target) = (function.clone(), *target);
            // The successor reads the result first: only source sites and
            // storage ends, which lower to nothing, come before its return.
            if target == block
                || predecessors.get(target) != Some(&1)
                || !blocks[target]
                    .statements
                    .iter()
                    .all(|statement| matches!(statement, S::Site { .. } | S::EndStorage { .. }))
                || !reaches_return(target)
            {
                return;
            }
            let call = blocks
                .iter()
                .filter_map(|block| match &block.terminator {
                    T::Call {
                        result: Some(step), ..
                    } => Some(*step + 1),
                    _ => None,
                })
                .max()
                .unwrap_or(0);
            if let T::Call { result, .. } = &mut blocks[block].terminator {
                *result = Some(call);
            }
            blocks[target].terminator = T::ReturnValue {
                value: E::CallResult {
                    call,
                    function,
                    keeps: false,
                },
            };
        }
    }
    locals.retain(|local| local.name != return_place);
}

/// Whether a value of `value_type` is returned as itself, a scalar.
fn returned_directly(value_type: &super::super::schema::Type) -> bool {
    use super::super::schema::Type;
    matches!(
        value_type,
        Type::I8
            | Type::I16
            | Type::I32
            | Type::I64
            | Type::Isize
            | Type::U8
            | Type::U16
            | Type::U32
            | Type::U64
            | Type::Usize
            | Type::Bool
            | Type::Enum { .. }
    )
}

/// Binds a slice loop's variable where `next` yields, as
/// [`bind_range_payloads`] does for a range: once the protocol has split a
/// slice iterator's `next` into its two outcomes, the `Option` it returns is
/// read only by the `Some` arm's first statement, `x = (opt as Some).0`, and
/// by the tag test the split left unreachable. The yielding outcome then
/// assigns `x` the element's reference itself (`payload: Some(x)`), the
/// other outcome is nothing, and the `Option`, its tag test and its
/// temporary go.
pub(super) fn bind_slice_payloads(
    locals: &mut Vec<Place>,
    blocks: &mut [MirBlock],
    temporaries: &BTreeSet<String>,
) {
    let transparent = |statement: &S| {
        matches!(
            statement,
            S::BeginStorage { .. } | S::EndStorage { .. } | S::Site { .. }
        )
    };
    // A block that tests the `Option`'s tag, which the split replaced.
    let tests = |block: &MirBlock, option: &str| matches!(&block.terminator, T::If { condition: E::SharedArrayOptionTag { option: tested }, .. } if tested == option);
    let mut removed = BTreeSet::new();
    for index in 0..blocks.len() {
        let (option, target) = match (blocks[index].statements.last(), &blocks[index].terminator) {
            (
                Some(S::SharedArrayNext {
                    option: Some(option),
                    payload: None,
                    taken: Some(true),
                    ..
                }),
                T::Goto { target },
            ) => (option.clone(), *target),
            _ => continue,
        };
        if !temporaries.contains(&option) || removed.contains(&option) {
            continue;
        }
        // The `Some` arm's binding of the element, `x = (opt as Some).0`,
        // when its first statement is one; a `Some(_)` arm binds nothing.
        let binding = blocks[target]
            .statements
            .iter()
            .position(|statement| !transparent(statement))
            .and_then(|position| match &blocks[target].statements[position] {
                S::Assign {
                    target: E::Local { name: payload },
                    value: E::SharedArrayOptionElement { option: read },
                } if *read == option => Some((position, payload.clone())),
                _ => None,
            });
        // Nothing else names the `Option`: its `next` outcomes, each decided,
        // the binding, and the replaced tag test and its tag copies.
        let mut nexts = 0;
        let mut others = 0;
        for (number, block) in blocks.iter().enumerate() {
            let replaced = tests(block, &option);
            for (place, statement) in block.statements.iter().enumerate() {
                if transparent(statement) || !mentioned_locals(statement).contains(&option) {
                    continue;
                }
                match statement {
                    S::SharedArrayNext { taken: Some(_), .. } => nexts += 1,
                    S::Assign {
                        value: E::SharedArrayOptionTag { .. },
                        ..
                    } if replaced => {}
                    _ if binding
                        .as_ref()
                        .is_some_and(|(position, _)| number == target && place == *position) => {}
                    _ => others += 1,
                }
            }
            if !replaced {
                let mut reads = BTreeMap::new();
                let mut named = BTreeSet::new();
                terminator_uses(&block.terminator, &mut reads, &mut named);
                if reads.contains_key(&option) || named.contains(&option) {
                    others += 1;
                }
            }
        }
        if others != 0 || nexts != 2 {
            continue;
        }
        if let Some((position, _)) = &binding {
            blocks[target].statements.remove(*position);
        }
        let payload = binding.map(|(_, payload)| payload);
        for block in blocks.iter_mut() {
            if tests(block, &option) {
                block.statements.retain(|statement| !matches!(statement, S::Assign { value: E::SharedArrayOptionTag { option: tag }, .. } if *tag == option));
                block.terminator = T::Unreachable;
            }
            for statement in &mut block.statements {
                if let S::SharedArrayNext {
                    option: next_option,
                    payload: next_payload,
                    taken,
                    ..
                } = statement
                    && next_option.as_deref() == Some(option.as_str())
                {
                    *next_option = None;
                    if *taken == Some(true) {
                        next_payload.clone_from(&payload);
                    }
                }
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

/// Builds each iterator in the local the program moves it into. MIR builds
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
            // Every iterator kind moves as a plain value: its fields.
            if !matches!(
                kind,
                IteratorKind::Range
                    | IteratorKind::Chunk
                    | IteratorKind::SharedArray
                    | IteratorKind::Enumerate
            ) || !temporaries.contains(&source)
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
    // Each local's mentions apart from storage markers and the call that
    // defines it: a tested-then-read result has exactly its test and its read.
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
        let mut terminator_reads = BTreeMap::new();
        let mut terminator_named = BTreeSet::new();
        terminator_uses(
            &block.terminator,
            &mut terminator_reads,
            &mut terminator_named,
        );
        terminator_named.extend(terminator_reads.into_keys());
        if let Some(destination) = call_destination(&block.terminator) {
            terminator_named.remove(destination);
        }
        for name in terminator_named {
            *mentions.entry(name).or_default() += 1;
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
        // A result its successor tests for a variant, then reads once in the
        // arm that variant takes, as a `for` loop's `match` on `next()` does:
        // the test keeps the result and the arm's read ends it.
        if temporaries.contains(&destination)
            && assigned.get(&destination) == Some(&1)
            && mentions.get(&destination) == Some(&2)
            && target != index
            && predecessors.get(target) == Some(&1)
            && let Some((arm, position)) =
                tested_then_read(blocks, &destination, target, &predecessors)
        {
            let call = next_step;
            let result = |keeps| E::CallResult {
                call,
                function: function.clone(),
                keeps,
            };
            if let T::If {
                condition: E::VariantIs { value, .. },
                ..
            } = &mut blocks[target].terminator
            {
                **value = result(true);
            }
            if let S::Assign {
                value: E::EnumField { base, .. },
                ..
            } = &mut blocks[arm].statements[position]
            {
                **base = result(false);
            }
            if let T::Call { result, .. } = &mut blocks[index].terminator {
                *result = Some(call);
            }
            next_step += 1;
            removed.insert(destination);
            continue;
        }
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
        let mut values = BTreeMap::from([(
            destination.clone(),
            E::CallResult {
                call,
                function,
                keeps: false,
            },
        )]);
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

/// The arm a test of `destination`'s variant takes when it holds, and the
/// position there of the arm's one read of it, its payload: `(arm, i)` when
/// `dispatch` only tests `destination` and the arm, entered only from that
/// test, reads its field first.
fn tested_then_read(
    blocks: &[MirBlock],
    destination: &str,
    dispatch: usize,
    predecessors: &[usize],
) -> Option<(usize, usize)> {
    let transparent = |statement: &S| {
        matches!(
            statement,
            S::Site { .. } | S::BeginStorage { .. } | S::EndStorage { .. }
        )
    };
    let block = blocks.get(dispatch)?;
    let T::If {
        condition: E::VariantIs { value, variant },
        then_target,
        ..
    } = &block.terminator
    else {
        return None;
    };
    if !matches!(value.as_ref(), E::Local { name } if name == destination)
        || !block.statements.iter().all(transparent)
        || predecessors.get(*then_target) != Some(&1)
    {
        return None;
    }
    let arm = blocks.get(*then_target)?;
    let position = arm
        .statements
        .iter()
        .position(|statement| !transparent(statement))?;
    let S::Assign {
        value: E::EnumField {
            base,
            variant: read,
            ..
        },
        ..
    } = &arm.statements[position]
    else {
        return None;
    };
    (matches!(base.as_ref(), E::Local { name } if name == destination) && read == variant)
        .then_some((*then_target, position))
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
        T::Return | T::ReturnValue { .. } | T::Unreachable | T::Panic { .. } => Vec::new(),
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
        // The test reads its value as a pure scalar test does.
        E::VariantIs { value, .. } => pure(value),
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
        S::EnumerateNext { iterator, option } | S::ChunkNext { iterator, option } => {
            vec![iterator, option]
        }
        S::SharedArrayNext {
            iterator,
            option,
            payload,
            ..
        } => std::iter::once(iterator)
            .chain(option)
            .chain(payload)
            .collect(),
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
        T::ReturnValue { value } => vec![value],
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
        | T::ReturnValue { .. }
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
        E::VariantIs { value, .. } => vec![value],
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
        E::VariantIs { value, .. } => vec![value],
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
    use std::collections::{BTreeMap, BTreeSet};

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
                if matches!(left.as_ref(), E::CallResult { call: 0, function, .. } if function == "f")
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

    fn block(statements: Vec<S>, terminator: T) -> MirBlock {
        MirBlock {
            terminator_site: None,
            statements,
            terminator,
        }
    }
    /// Runs the return-place pass over `blocks`, with locals `_0` and `x`.
    fn returned(mut blocks: Vec<MirBlock>) -> (Vec<String>, Vec<MirBlock>) {
        let mut locals = ["__rust_mir_0", "x"].map(place).to_vec();
        super::return_values(&mut locals, &mut blocks, "__rust_mir_0");
        (locals.into_iter().map(|local| local.name).collect(), blocks)
    }

    #[test]
    fn a_value_written_just_before_return_is_returned() {
        // `_0 = x + 1; goto 1;  1: StorageDead(x); return` is `return x + 1`.
        let (locals, blocks) = returned(vec![
            block(
                vec![assign(
                    "__rust_mir_0",
                    binary(
                        "add",
                        local("x"),
                        E::UnsignedInteger {
                            value: 1,
                            value_type: Type::U32,
                        },
                    ),
                )],
                T::Goto { target: 1 },
            ),
            block(vec![S::EndStorage { local: "x".into() }], T::Return),
        ]);
        assert_eq!(locals, ["x"]);
        assert!(blocks[0].statements.is_empty());
        assert!(matches!(
            &blocks[0].terminator,
            T::ReturnValue { value: E::Binary { operator, .. } } if operator == "add"
        ));
    }

    #[test]
    fn a_tail_call_returns_its_step_result() {
        // `_0 = f(x) -> 1;  1: return` is `return f(x)`, the call a step.
        let (locals, blocks) = returned(vec![
            block(
                vec![],
                T::Call {
                    function: "f".into(),
                    arguments: vec![local("x")],
                    owned_arguments: vec![],
                    destination: "__rust_mir_0".into(),
                    target: 1,
                    through_pointer: false,
                    result: None,
                },
            ),
            block(vec![], T::Return),
        ]);
        assert_eq!(locals, ["x"]);
        assert!(matches!(
            &blocks[0].terminator,
            T::Call {
                result: Some(0),
                ..
            }
        ));
        assert!(matches!(
            &blocks[1].terminator,
            T::ReturnValue {
                value: E::CallResult {
                    call: 0,
                    keeps: false,
                    ..
                }
            }
        ));
    }

    #[test]
    fn a_return_place_written_on_two_paths_stays_a_local() {
        // `if x { _0 = 0 } else { _0 = 1 }; return`: both arms reach one
        // return, so the place keeps its local.
        let zero = E::UnsignedInteger {
            value: 0,
            value_type: Type::U32,
        };
        let (locals, blocks) = returned(vec![
            block(
                vec![],
                T::If {
                    condition: local("x"),
                    then_target: 1,
                    else_target: 2,
                },
            ),
            block(
                vec![assign("__rust_mir_0", zero.clone())],
                T::Goto { target: 3 },
            ),
            block(vec![assign("__rust_mir_0", zero)], T::Goto { target: 3 }),
            block(vec![], T::Return),
        ]);
        assert_eq!(locals, ["__rust_mir_0", "x"]);
        assert!(matches!(blocks[3].terminator, T::Return));
    }

    #[test]
    fn unused_temporaries_and_unit_call_results_are_removed() {
        // `StorageLive(t1); StorageDead(t1); t2 = f(x) -> 1;  1: return`,
        // with `t2: ()`: neither temporary holds anything a later step reads.
        let mut locals = vec![
            place("x"),
            place("t1"),
            Place {
                value_type: Type::Unit,
                ..place("t2")
            },
            place("t3"),
        ];
        let mut blocks = vec![
            MirBlock {
                terminator_site: None,
                statements: vec![
                    S::BeginStorage { local: "t1".into() },
                    S::EndStorage { local: "t1".into() },
                    assign("t3", local("x")),
                ],
                terminator: T::Call {
                    function: "f".into(),
                    arguments: vec![local("t3")],
                    owned_arguments: vec![],
                    destination: "t2".into(),
                    target: 1,
                    through_pointer: false,
                    result: None,
                },
            },
            MirBlock {
                terminator_site: None,
                statements: vec![],
                terminator: T::Return,
            },
        ];
        let temporaries = BTreeSet::from(["t1".into(), "t2".into(), "t3".into()]);
        super::remove_unused(&mut locals, &mut blocks, &temporaries);
        let names: Vec<_> = locals.iter().map(|local| local.name.as_str()).collect();
        assert_eq!(names, ["x", "t3"]);
        assert_eq!(blocks[0].statements.len(), 1);
    }

    /// Runs the unchanging-value pass with parameter `p` and temporaries
    /// `t1` and `t2`.
    fn substituted_everywhere(blocks: Vec<MirBlock>) -> (Vec<String>, Vec<MirBlock>) {
        let mut locals = ["x", "t1", "t2"].map(place).to_vec();
        let mut blocks = blocks;
        let temporaries = BTreeSet::from(["t1".into(), "t2".into()]);
        let parameters = BTreeMap::from([("p".into(), Type::U32)]);
        super::substitute_literals(&mut locals, &mut blocks, &temporaries, &parameters);
        (locals.into_iter().map(|local| local.name).collect(), blocks)
    }

    #[test]
    fn a_literal_temporary_is_read_as_its_literal_everywhere() {
        // `t1 = 3; x = t1 + t1;` reads the literal twice.
        let three = E::UnsignedInteger {
            value: 3,
            value_type: Type::U32,
        };
        let (locals, blocks) = substituted_everywhere(vec![block(
            vec![
                assign("t1", three),
                assign("x", binary("add", local("t1"), local("t1"))),
            ],
            T::Return,
        )]);
        assert_eq!(locals, ["x", "t2"]);
        assert!(matches!(
            blocks[0].statements.as_slice(),
            [S::Assign { value: E::Binary { left, right, .. }, .. }]
                if matches!(left.as_ref(), E::UnsignedInteger { value: 3, .. })
                    && matches!(right.as_ref(), E::UnsignedInteger { value: 3, .. })
        ));
    }

    #[test]
    fn a_copy_of_an_unchanged_parameter_is_read_in_a_later_block() {
        // `t1 = p; goto 1;  1: x = t1;` is `x = p`; `t2 = x` copies a
        // local the body writes, so it stays.
        let (locals, blocks) = substituted_everywhere(vec![
            block(
                vec![assign("t1", local("p")), assign("t2", local("x"))],
                T::Goto { target: 1 },
            ),
            block(
                vec![assign("x", local("t1")), assign("x", local("t2"))],
                T::Return,
            ),
        ]);
        assert_eq!(locals, ["x", "t2"]);
        assert!(matches!(
            &blocks[1].statements[0],
            S::Assign { value: E::Local { name }, .. } if name == "p"
        ));
    }

    #[test]
    fn a_reborrow_of_a_borrowed_local_is_that_borrow_at_every_read() {
        // `t2 = &mut x; t1 = &mut *t2; f(t1) -> 1;  1: g(t1)` passes `&mut x`
        // to both calls.
        let reference = Type::Reference {
            mutable: true,
            pointee: Box::new(Type::U32),
        };
        let borrow = |place: E| E::Borrow {
            place: Box::new(place),
            value_type: reference.clone(),
        };
        let call = |function: &str, target| T::Call {
            function: function.into(),
            arguments: vec![local("t1")],
            owned_arguments: vec![],
            destination: "unit".into(),
            target,
            through_pointer: false,
            result: None,
        };
        let mut locals = vec![
            place("x"),
            Place {
                value_type: reference.clone(),
                ..place("t1")
            },
            Place {
                value_type: reference.clone(),
                ..place("t2")
            },
        ];
        let mut blocks = vec![
            block(
                vec![
                    assign("t2", borrow(local("x"))),
                    assign(
                        "t1",
                        borrow(E::Deref {
                            reference: Box::new(local("t2")),
                            value_type: Type::U32,
                        }),
                    ),
                ],
                call("f", 1),
            ),
            block(vec![], call("g", 2)),
            block(vec![], T::Return),
        ];
        let temporaries = BTreeSet::from(["t1".into(), "t2".into()]);
        super::substitute_literals(&mut locals, &mut blocks, &temporaries, &BTreeMap::new());
        let names: Vec<_> = locals.iter().map(|local| local.name.as_str()).collect();
        assert_eq!(names, ["x"]);
        for block in &blocks[..2] {
            assert!(matches!(
                &block.terminator,
                T::Call { arguments, .. } if matches!(
                    arguments.as_slice(),
                    [E::Borrow { place, .. }] if matches!(place.as_ref(), E::Local { name } if name == "x")
                )
            ));
        }
    }

    #[test]
    fn a_pure_value_written_to_a_temporary_no_one_reads_is_removed() {
        // `t1 = x < 3; return`: the comparison is never read.
        let mut locals = vec![place("x"), place("t1")];
        let mut blocks = vec![block(
            vec![
                S::BeginStorage { local: "t1".into() },
                assign(
                    "t1",
                    binary(
                        "lt",
                        local("x"),
                        E::UnsignedInteger {
                            value: 3,
                            value_type: Type::U32,
                        },
                    ),
                ),
                S::EndStorage { local: "t1".into() },
            ],
            T::Return,
        )];
        super::remove_unused(&mut locals, &mut blocks, &BTreeSet::from(["t1".into()]));
        assert_eq!(locals.len(), 1);
        assert!(blocks[0].statements.is_empty());
    }

    #[test]
    fn a_shared_slice_borrow_and_its_length_are_read_in_place() {
        // `t1 = &bytes; t2 = len(t1); x = t2`, with `bytes: &[u8]` a
        // parameter only borrowed shared, is `x = len(&bytes)`.
        let slice = Type::ByteSlice { mutable: false };
        let mut locals = vec![
            place("x"),
            Place {
                value_type: slice.clone(),
                ..place("t1")
            },
            Place {
                value_type: Type::Usize,
                ..place("t2")
            },
        ];
        let mut blocks = vec![block(
            vec![
                assign(
                    "t1",
                    E::Borrow {
                        place: Box::new(local("bytes")),
                        value_type: slice.clone(),
                    },
                ),
                assign(
                    "t2",
                    E::SliceLength {
                        slice: Box::new(local("t1")),
                    },
                ),
                assign("x", local("t2")),
            ],
            T::Return,
        )];
        let temporaries = BTreeSet::from(["t1".into(), "t2".into()]);
        let parameters = BTreeMap::from([("bytes".into(), slice)]);
        super::substitute_literals(&mut locals, &mut blocks, &temporaries, &parameters);
        let names: Vec<_> = locals.iter().map(|local| local.name.as_str()).collect();
        assert_eq!(names, ["x"]);
        assert!(matches!(
            blocks[0].statements.as_slice(),
            [S::Assign { value: E::SliceLength { slice }, .. }]
                if matches!(slice.as_ref(), E::Borrow { place, .. }
                    if matches!(place.as_ref(), E::Local { name } if name == "bytes"))
        ));
    }
}
