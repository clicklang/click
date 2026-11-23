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
    Expression as E, MirBlock, MirBody, MirCallee, MirLocalId, MirStatement as S,
    MirTerminator as T, Place, Type,
};
use std::collections::{BTreeMap, BTreeSet};

/// The nullable box tested by a MIR branch for `Some`.
pub(in crate::languages::rust) fn tested_option_box_local(condition: &E) -> Option<&MirLocalId> {
    let E::Binary {
        operator,
        left_type: Type::OptionBox { .. },
        right_type: Type::OptionBox { .. },
        left,
        right,
    } = condition
    else {
        return None;
    };
    if operator == "ne"
        && matches!(right.as_ref(), E::NoneBox)
        && let E::Local { name } = left.as_ref()
    {
        Some(name)
    } else {
        None
    }
}

/// Select scalar expression results with one producer and reads along one
/// straight-line fragment, or one producer per arm of a two-way branch
/// followed by reads in its continuation. The final reader ends the result. A slot read
/// through its address, written by another operation, or live across a
/// control-flow edge where other paths can enter still needs storage.
/// A box pointer can also be retained for a single assignment or field drop.
pub(in crate::languages::rust) fn scalar_expression_operands(
    mir: &MirBody,
    loop_tests: &BTreeSet<usize>,
) -> BTreeMap<MirLocalId, super::super::borrow_frontiers::MirPoint> {
    use super::super::borrow_frontiers::MirPoint;
    if mir.unnamed_locals.is_empty() {
        return BTreeMap::new();
    }
    let is_candidate = |name: &MirLocalId| mir.unnamed_locals.contains(name);
    let mut definitions = BTreeMap::<_, Vec<_>>::new();
    let mut reads_by_local = BTreeMap::new();
    let mut excluded = BTreeSet::new();
    let mut crosses_fragment = BTreeSet::new();

    // A forward goto or direct call into a block with exactly one incoming
    // edge continues the fragment. A call can change what the producer read,
    // but the captured value has already been evaluated. A join or a loop
    // back edge starts another fragment.
    let mut incoming = vec![0usize; mir.blocks.len()];
    let mut predecessor = vec![None; mir.blocks.len()];
    for (index, block) in mir.blocks.iter().enumerate() {
        for successor in successors(&block.terminator) {
            if let Some(count) = incoming.get_mut(successor) {
                *count += 1;
            }
        }
        if let T::Goto { target }
        | T::Call {
            target,
            function: MirCallee::Direct(_),
            ..
        } = block.terminator
            && index < target
            && let Some(entry) = predecessor.get_mut(target)
        {
            *entry = Some(index);
        }
    }
    // Each arm and the join must have exactly the incoming edges of this
    // branch. The forward edges also exclude a loop back edge.
    let mut joins = BTreeMap::new();
    for (header, block) in mir.blocks.iter().enumerate() {
        let T::If {
            then_target,
            else_target,
            ..
        } = block.terminator
        else {
            continue;
        };
        let (lo, hi) = (then_target.min(else_target), then_target.max(else_target));
        if !(header < lo && lo < hi) || incoming.get(hi) != Some(&1) || incoming[lo] != 1 {
            continue;
        }
        let T::Goto { target: join } = mir.blocks[lo].terminator else {
            continue;
        };
        if hi < join
            && incoming.get(join) == Some(&2)
            && matches!(mir.blocks[hi].terminator, T::Goto { target } if target == join)
        {
            joins.insert((lo, hi), join);
        }
    }

    let mut fragments: Vec<usize> = Vec::with_capacity(mir.blocks.len());
    for (block, code) in mir.blocks.iter().enumerate() {
        let fragment = match predecessor[block] {
            Some(previous) if incoming[block] == 1 => fragments[previous],
            _ => block,
        };
        fragments.push(fragment);
        let statements = code.statements.iter().map(Some).chain([None]);
        for (statement, code_or_terminal) in statements.enumerate() {
            let point = MirPoint { block, statement };
            if let Some(S::Assign {
                target: E::Local { name },
                value,
            }) = code_or_terminal
                && is_candidate(name)
            {
                if matches!(value, E::Call { .. } | E::ClosureInstance { .. }) {
                    excluded.insert(name.clone());
                } else {
                    definitions.entry(name).or_default().push(point);
                }
            }
            let mut reads = BTreeMap::new();
            let value_reader = if let Some(statement) = code_or_terminal {
                statement_uses(statement, &mut reads, &mut excluded);
                matches!(
                    statement,
                    S::Assert { .. }
                        | S::Assign { .. }
                        | S::Initialize { .. }
                        | S::SliceSplit { .. }
                )
            } else if let T::BoxFree { local, .. } = &code.terminator {
                reads.insert(local.clone(), 1);
                true
            } else {
                terminator_uses(&code.terminator, &mut reads, &mut excluded);
                excluded.extend(call_destination(&code.terminator).cloned());
                matches!(
                    code.terminator,
                    T::ReturnValue { .. }
                        | T::Call {
                            function: MirCallee::Direct(_),
                            ..
                        }
                ) || matches!(&code.terminator, T::If { condition, .. }
                    if !loop_tests.contains(&block) && (straight_line_scalar(condition) || tested_option_box_local(condition).is_some()))
            };
            for (name, count) in reads {
                if !is_candidate(&name) {
                    continue;
                }
                if !value_reader {
                    excluded.insert(name);
                    continue;
                }
                let uses = reads_by_local
                    .entry(name.clone())
                    .or_insert((point, point, count, 0usize));
                if fragments[uses.0.block] != fragment {
                    crosses_fragment.insert(name);
                }
                uses.1 = point;
                uses.2 = count;
                uses.3 += count;
            }
        }
    }

    mir.locals
        .iter()
        .filter_map(|local| {
            let name = &local.name;
            if excluded.contains(name) {
                return None;
            }
            let &(first, last, last_read_count, total_reads) = reads_by_local.get(name)?;
            if last_read_count != 1 {
                return None;
            }
            let producers = definitions.get(name)?.as_slice();
            let boxed = matches!(local.value_type, Type::Box { .. } | Type::OptionBox { .. });
            if crosses_fragment.contains(name) {
                let [producer] = producers else { return None };
                return (matches!(local.value_type, Type::OptionBox { .. })
                    && total_reads == 2
                    && *producer < first
                    && fragments[producer.block] == fragments[first.block]
                    && first.statement == mir.blocks[first.block].statements.len()
                    && !loop_tests.contains(&first.block)
                    && matches!(&mir.blocks[first.block].terminator,
                        T::If { condition, then_target, else_target }
                            if tested_option_box_local(condition) == Some(name)
                                && then_target != else_target
                                && first.block < *then_target
                                && *then_target == last.block
                                && incoming[last.block] == 1)
                    && matches!(&mir.blocks[producer.block].statements[producer.statement],
                        S::Assign { value: E::Field { .. } | E::Local { .. }, .. })
                    && matches!(mir.blocks[last.block].statements.get(last.statement),
                        Some(S::Assign { target: E::Local { .. }, value: E::Local { name: source } })
                            if source == name))
                .then(|| (name.clone(), last));
            }
            if !local.value_type.is_scalar() {
                let [producer] = producers else { return None };
                if !boxed || first != last {
                    return None;
                }
                let S::Assign { value, .. } = &mir.blocks[producer.block].statements[producer.statement]
                else { return None };
                let reader = &mir.blocks[last.block];
                let supported = match reader.statements.get(last.statement) {
                    Some(S::Assign { value: E::Local { name: source }, .. }) if source == name => {
                        matches!(value, E::Local { .. } | E::Field { .. } | E::CallResult { .. })
                    }
                    None => matches!(value, E::Field { .. }) && matches!(&reader.terminator, T::BoxFree { local, .. } if local == name),
                    _ => false,
                };
                if !supported {
                    return None;
                }
            }
            let reaches_reader = match producers {
                [producer] => {
                    // An intervening drop can run arbitrary glue. A captured
                    // box pointer still denotes the value read before the drop.
                    let continues_after_drop = boxed && incoming[first.block] == 1
                        && matches!(&mir.blocks[producer.block].terminator,
                            T::BoxFree { target, .. } if *target == first.block);
                    (fragments[producer.block] == fragments[first.block] || continues_after_drop)
                        && *producer < first
                }
                [left, right] => {
                    // Both tails publish the result. This gives diagnostics
                    // and proofs the branch region as its single source.
                    let &join = joins.get(&(left.block, right.block))?;
                    fragments[first.block] == join
                        && [left, right].into_iter().all(|point| {
                            mir.blocks[point.block].statements[point.statement + 1..]
                                .iter()
                                .all(|s| matches!(s, S::Site { .. }))
                        })
                }
                _ => false,
            };
            reaches_reader.then(|| (name.clone(), last))
        })
        .collect()
}

/// Substitutes each pure temporary of `temporaries` into its one read, and
/// removes it from `locals` and its block.
pub(super) fn substitute_pure_values(
    locals: &mut Vec<Place>,
    blocks: &mut [MirBlock],
    temporaries: &BTreeSet<MirLocalId>,
    constant_initializers: &BTreeSet<String>,
) {
    // How each temporary is used: read by an expression, or named by a
    // statement or terminator field, which no substitution can reach.
    let mut reads = BTreeMap::<MirLocalId, usize>::new();
    let mut named = BTreeSet::<MirLocalId>::new();
    let mut switch_locals = BTreeSet::new();
    let mut assignments = BTreeMap::<MirLocalId, usize>::new();
    let mut predecessors = vec![0usize; blocks.len()];
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
        if let Some(name) = enum_switch_local(&block.terminator) {
            // Keep enum scrutinees out of general substitution, but count
            // the switch as a read for the adjacent borrowed-match rewrite.
            switch_locals.insert(name.clone());
            *reads.entry(name.clone()).or_default() += 1;
        } else {
            terminator_uses(&block.terminator, &mut reads, &mut named);
        }
        if let Some(destination) = call_destination(&block.terminator) {
            named.insert(destination.clone());
        }
        for successor in successors(&block.terminator) {
            if let Some(count) = predecessors.get_mut(successor) {
                *count += 1;
            }
        }
    }
    let single_read = |name: &MirLocalId| {
        temporaries.contains(name)
            && !named.contains(name)
            && reads.get(name) == Some(&1)
            && assignments.get(name) == Some(&1)
    };
    let substitutable = |name: &MirLocalId| single_read(name) && !switch_locals.contains(name);
    let mut removed = BTreeSet::new();
    for block in blocks.iter_mut() {
        // The pure values defined so far in this block whose read is still
        // ahead, with nothing since that could change them.
        let mut pending = BTreeMap::<MirLocalId, E>::new();
        let mut kept = Vec::with_capacity(block.statements.len());
        // A borrow is the value its one read takes whole: an argument of the
        // block's call, `f(&mut x)`, whose borrow lasts the call, or a local's
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
                    // A record's first field takes the reference whole and
                    // writes it before preparing any later field.
                    S::Initialize { fields, .. } => match fields.first() {
                        Some(E::Local { name }) => Some(name.clone()),
                        _ => None,
                    },
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
        // An array value, `[v; 4]` or `[a, b]`, is the value its one read
        // takes whole: a field of a record the block initializes, which the
        // lowering writes from the array expression itself.
        let field_readers = block
            .statements
            .iter()
            .filter_map(|statement| match statement {
                S::Initialize { fields, .. } => Some(fields),
                _ => None,
            })
            .flatten()
            .filter_map(|field| match field {
                E::Local { name } => Some(name.clone()),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        // The pending borrows of a place rooted at a local, by that local:
        // the place's address is the same until a statement names the local.
        let mut rooted = BTreeMap::<MirLocalId, MirLocalId>::new();
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
                            && borrow_readers.contains(name))
                        || (pure_array(value) && field_readers.contains(name))) =>
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
        // Finish collapsing reborrow chains before moving their final
        // borrow into a slice operation.
        fold_adjacent_slice_borrows(&mut block.statements, &substitutable, &mut removed);
        fold_slice_coercion_operands(block, &substitutable, &mut removed);
        fold_closure_argument(block, &substitutable, &mut removed);
        if !constant_initializers.is_empty() {
            fold_constant_remainder_casts(
                &mut block.statements,
                &substitutable,
                constant_initializers,
                &mut removed,
            );
        }
    }
    fold_slice_iterator_successors(blocks, &predecessors, &substitutable, &mut removed);
    fold_scalar_successors(locals, blocks, &predecessors, &substitutable, &mut removed);
    for block in blocks.iter_mut() {
        fold_scalar_condition(block, &substitutable, &mut removed);
        fold_borrowed_enum_switch(block, &single_read, &mut removed);
        block.statements.retain(|statement| match statement {
            S::BeginStorage { local } | S::EndStorage { local } => !removed.contains(local),
            S::Assign {
                target: E::Local { name },
                ..
            } => !removed.contains(name),
            _ => true,
        });
    }
    locals.retain(|local| !removed.contains(&local.name));
}

/// A two-arm match can test a borrowed enum directly. The switch lowers to
/// one variant test, so the original load still runs exactly once.
fn fold_borrowed_enum_switch(
    block: &mut MirBlock,
    single_read: &impl Fn(&MirLocalId) -> bool,
    removed: &mut BTreeSet<MirLocalId>,
) {
    use super::super::schema::SwitchLabel;

    let T::Switch {
        scrutinee,
        cases,
        otherwise: None,
    } = &mut block.terminator
    else {
        return;
    };
    let E::Local { name } = scrutinee else { return };
    let [first, second] = cases.as_slice() else {
        return;
    };
    if first.target == second.target
        || !matches!(
            (&first.label, &second.label),
            (SwitchLabel::Variant { .. }, SwitchLabel::Variant { .. })
        )
        || !single_read(name)
    {
        return;
    }
    let Some(S::Assign {
        target: E::Local { name: target },
        value:
            value @ E::Deref {
                reference,
                value_type: Type::Enum { .. },
            },
    }) = block.statements.iter().rfind(|statement| match statement {
        S::Site { site } => Some(*site) != block.terminator_site,
        S::EndStorage { local } => local != name,
        _ => true,
    })
    else {
        return;
    };
    if target == name && matches!(reference.as_ref(), E::Local { .. }) {
        removed.insert(name.clone());
        *scrutinee = value.clone();
    }
}

/// Match constructor operands after earlier passes have simplified the
/// borrow and copy statements that feed them.
pub(super) fn fold_constructor_reborrows(
    locals: &mut Vec<Place>,
    blocks: &mut [MirBlock],
    temporaries: &BTreeSet<MirLocalId>,
) {
    if !blocks
        .iter()
        .flat_map(|block| &block.statements)
        .any(|statement| {
            matches!(statement, S::Initialize { fields, .. }
            if matches!(fields.first(), Some(E::Local { name }) if temporaries.contains(name)))
        })
    {
        return;
    }
    let mut reads = BTreeMap::new();
    let mut named = BTreeSet::new();
    let mut writes = BTreeMap::<MirLocalId, usize>::new();
    for block in blocks.iter() {
        for statement in &block.statements {
            statement_uses(statement, &mut reads, &mut named);
            if let S::Assign {
                target: E::Local { name },
                ..
            } = statement
            {
                *writes.entry(name.clone()).or_default() += 1;
            }
        }
        terminator_uses(&block.terminator, &mut reads, &mut named);
        named.extend(call_destination(&block.terminator).cloned());
    }
    let substitutable = |name: &MirLocalId| {
        temporaries.contains(name)
            && !named.contains(name)
            && reads.get(name) == Some(&1)
            && writes.get(name) == Some(&1)
    };
    let mut removed = BTreeSet::new();
    for block in blocks.iter_mut() {
        fold_constructor_reborrow(block, &substitutable, &mut removed);
    }
    if removed.is_empty() {
        return;
    }
    for block in blocks {
        block.statements.retain(|statement| match statement {
            S::Assign {
                target: E::Local { name },
                ..
            }
            | S::BeginStorage { local: name }
            | S::EndStorage { local: name } => !removed.contains(name),
            _ => true,
        });
    }
    locals.retain(|local| !removed.contains(&local.name));
}

/// A constructor can take a reborrow in its first field directly. A local
/// copy for another field can sit between them, but it cannot rebind the
/// reference used by the borrow.
fn fold_constructor_reborrow(
    block: &mut MirBlock,
    substitutable: &impl Fn(&MirLocalId) -> bool,
    removed: &mut BTreeSet<MirLocalId>,
) {
    let mut previous = None;
    let mut before_previous = None;
    for position in 0..block.statements.len() {
        let (earlier, later) = block.statements.split_at_mut(position);
        let statement = &mut later[0];
        if let S::Initialize { fields, .. } = statement
            && let Some(E::Local { name: read }) = fields.first_mut()
            && substitutable(read)
            && let Some(previous) = previous
        {
            let producer = match &earlier[previous] {
                S::Assign {
                    target: E::Local { name },
                    value: E::Local { .. },
                } if name != read => before_previous,
                _ => Some(previous),
            };
            if let Some(S::Assign {
                target: E::Local { name },
                value: borrow @ E::Borrow { place, .. },
            }) = producer.map(|producer| &earlier[producer])
                && name == read
                && let E::Deref { reference, .. } = place.as_ref()
                && let E::Local { name: parent } = reference.as_ref()
                && !matches!(&earlier[previous], S::Assign { target: E::Local { name }, .. }
                    if name == parent)
            {
                removed.insert(name.clone());
                fields[0] = borrow.clone();
            }
        }
        before_previous = previous;
        previous = Some(position);
    }
}

/// A borrow consumed by the adjacent slice operation is the operation's
/// input. Moving it across no statements preserves the borrowed place and,
/// for an array coercion, its reference view and mutability.
fn fold_adjacent_slice_borrows(
    statements: &mut Vec<S>,
    substitutable: &impl Fn(&MirLocalId) -> bool,
    removed: &mut BTreeSet<MirLocalId>,
) {
    let mut statements_iter = std::mem::take(statements).into_iter().peekable();
    while let Some(statement) = statements_iter.next() {
        if let S::Assign {
            target: E::Local { name },
            value: borrow @ E::Borrow { place, value_type },
        } = &statement
            && substitutable(name)
            && pure(place)
            && !checked(place)
            && let Some(consumer) = statements_iter.peek_mut()
        {
            let operand = match value_type {
                Type::Reference { pointee, .. }
                    if matches!(pointee.as_ref(), Type::Array { .. }) =>
                {
                    match consumer {
                        S::Assign {
                            target: E::Local { .. },
                            value: E::ArrayToSlice { array, .. },
                        } => Some(array.as_mut()),
                        _ => None,
                    }
                }
                Type::ByteSlice { mutable: false } | Type::ScalarSlice { mutable: false, .. } => {
                    match consumer {
                        S::Assign {
                            target: E::Local { .. },
                            value: E::SliceLength { slice },
                        } => Some(slice.as_mut()),
                        S::SharedArrayInitialize { source, .. } => Some(source),
                        _ => None,
                    }
                }
                _ => None,
            };
            if let Some(operand) = operand
                && matches!(operand, E::Local { name: read } if read == name)
            {
                *operand = borrow.clone();
                removed.insert(name.clone());
                continue;
            }
        }
        statements.push(statement);
    }
}

/// A closure built immediately for the first argument is evaluated there.
/// Restrict this to the first argument so its captures still run before
/// all other argument preparation.
fn fold_closure_argument(
    block: &mut MirBlock,
    substitutable: &impl Fn(&MirLocalId) -> bool,
    removed: &mut BTreeSet<MirLocalId>,
) {
    let T::Call {
        arguments,
        function: MirCallee::Direct(_),
        ..
    } = &mut block.terminator
    else {
        return;
    };
    let Some(argument @ E::Local { .. }) = arguments.first_mut() else {
        return;
    };
    let Some(S::Assign {
        target: E::Local { name },
        value: value @ E::ClosureInstance { .. },
    }) = block.statements.iter().rfind(
        |statement| !matches!(statement, S::Site { site } if Some(*site) == block.terminator_site),
    )
    else {
        return;
    };
    if matches!(argument, E::Local { name: read } if read == name) && substitutable(name) {
        *argument = value.clone();
        removed.insert(name.clone());
    }
}

/// A fixed-array coercion can supply the pointer and length directly to its
/// immediate consumer: a length read, iterator initialization, or sole call argument.
fn fold_slice_coercion_operands(
    block: &mut MirBlock,
    substitutable: &impl Fn(&MirLocalId) -> bool,
    removed: &mut BTreeSet<MirLocalId>,
) {
    let mut previous = None;
    for position in 0..block.statements.len() {
        let (earlier, later) = block.statements.split_at_mut(position);
        let statement = &mut later[0];
        let operand = match statement {
            S::Site { .. } | S::BeginStorage { .. } | S::EndStorage { .. } => continue,
            S::Assign {
                target: E::Local { .. },
                value: E::SliceLength { slice },
            } => Some(slice.as_mut()),
            S::SharedArrayInitialize { source, .. } => Some(source),
            _ => None,
        };
        if let (Some(previous), Some(operand)) = (previous, operand) {
            inline_slice_coercion(&earlier[previous..], operand, true, substitutable, removed);
        }
        previous = Some(position);
    }
    if let Some(previous) = previous
        && let T::Call { arguments, .. } = &mut block.terminator
        && let [argument] = arguments.as_mut_slice()
    {
        inline_slice_coercion(
            &block.statements[previous..],
            argument,
            false,
            substitutable,
            removed,
        );
    }
}

/// Find the storage used by a local array or a borrowed array place. Field
/// selections and dereferences can be carried into the consumer unchanged.
fn array_coercion_root(array: &E) -> Option<&MirLocalId> {
    let mut place = match array {
        E::Local { name } => return Some(name),
        E::Borrow {
            place,
            value_type: Type::Reference { pointee, .. },
        } if matches!(pointee.as_ref(), Type::Array { .. }) => place.as_ref(),
        _ => return None,
    };
    loop {
        place = match place {
            E::Local { name } => return Some(name),
            E::Deref { reference, .. } => reference,
            E::Field { base, .. } => base,
            _ => return None,
        };
    }
}

/// The intervening markers must keep the source array live through the read.
fn inline_slice_coercion(
    statements: &[S],
    operand: &mut E,
    shared_only: bool,
    substitutable: &impl Fn(&MirLocalId) -> bool,
    removed: &mut BTreeSet<MirLocalId>,
) {
    let S::Assign {
        target: E::Local { name },
        value: value @ E::ArrayToSlice { array, mutable },
    } = &statements[0]
    else {
        return;
    };
    if (shared_only && *mutable)
        || !matches!(operand, E::Local { name: read } if read == name)
        || !substitutable(name)
        || removed.contains(name)
    {
        return;
    }
    let Some(source) = array_coercion_root(array) else {
        return;
    };
    if statements[1..].iter().any(|statement| {
        matches!(statement, S::BeginStorage { local } | S::EndStorage { local } if local == source || local == name)
    }) {
        return;
    }
    *operand = value.clone();
    removed.insert(name.clone());
}

/// Normalizing Iterator::iter can leave a goto (and one storage-only bridge)
/// between the coercion and initialization. Rejoin those fragments of the
/// same source statement. A storage-dead marker for the consumed temporary
/// can go away with the temporary, while the array's storage stays live.
fn fold_slice_iterator_successors(
    blocks: &mut [MirBlock],
    predecessors: &[usize],
    substitutable: &impl Fn(&MirLocalId) -> bool,
    removed: &mut BTreeSet<MirLocalId>,
) {
    for index in 0..blocks.len() {
        let block = &blocks[index];
        let (T::Goto { target }, Some(site)) = (&block.terminator, block.terminator_site) else {
            continue;
        };
        let Some((last, assignment)) =
            block.statements.iter().enumerate().rfind(|(_, statement)| {
                !matches!(
                    statement,
                    S::Site { .. } | S::BeginStorage { .. } | S::EndStorage { .. }
                )
            })
        else {
            continue;
        };
        let S::Assign {
            target: E::Local { name },
            value:
                value @ E::ArrayToSlice {
                    array,
                    mutable: false,
                },
        } = assignment
        else {
            continue;
        };
        if !substitutable(name)
            || removed.contains(name)
            || array_coercion_root(array).is_none_or(|source| source == name)
        {
            continue;
        }
        let transparent = |statement: &S| match statement {
            S::Site { site: marker } => *marker == site,
            S::EndStorage { local } => local == name,
            _ => false,
        };
        if !block.statements[last + 1..].iter().all(transparent) {
            continue;
        }
        let mut previous = index;
        let mut target = *target;
        for _ in 0..2 {
            if target <= previous || predecessors.get(target) != Some(&1) {
                break;
            }
            let consumer = &blocks[target];
            match consumer.statements.iter().position(|s| !transparent(s)) {
                Some(position) => {
                    if let S::SharedArrayInitialize {
                        source: E::Local { name: read },
                        ..
                    } = &consumer.statements[position]
                        && read == name
                    {
                        let name = name.clone();
                        let value = value.clone();
                        if let S::SharedArrayInitialize { source, .. } =
                            &mut blocks[target].statements[position]
                        {
                            *source = value;
                            removed.insert(name);
                        }
                    }
                    break;
                }
                None => {
                    let T::Goto { target: next } = consumer.terminator else {
                        break;
                    };
                    previous = target;
                    target = next;
                }
            }
        }
    }
}

/// A scalar copy or intrinsic can leave a goto between the expression and
/// its use. Rejoin the fragments of the same written statement when the
/// successor has one entry and no intervening effect can change the value.
fn fold_scalar_successors(
    locals: &[Place],
    blocks: &mut [MirBlock],
    predecessors: &[usize],
    substitutable: &impl Fn(&MirLocalId) -> bool,
    removed: &mut BTreeSet<MirLocalId>,
) {
    let scalars: BTreeSet<_> = locals
        .iter()
        .filter(|local| local.value_type.is_integer() || local.value_type == Type::Bool)
        .map(|local| &local.name)
        .collect();
    for index in 0..blocks.len() {
        let T::Goto { target } = blocks[index].terminator else {
            continue;
        };
        if target == 0 || predecessors.get(target) != Some(&1) {
            continue;
        }
        let Ok([definition, consumer]) = blocks.get_disjoint_mut([index, target]) else {
            continue;
        };
        let Some((last, earlier)) = definition.statements.split_last() else {
            continue;
        };
        // A loop test can compute its length after copying the index. This
        // metadata read neither rebinds the index nor evaluates user code.
        let previous_copy = match last {
            S::Assign {
                target: E::Local { name },
                value: length @ E::SliceLength { .. },
            } if is_movable_scalar_intrinsic(length) => {
                earlier.last().map(|statement| (statement, Some(name)))
            }
            _ => None,
        };
        for (assignment, length_target) in std::iter::once((last, None)).chain(previous_copy) {
            let S::Assign {
                target: E::Local { name },
                value: result,
            } = assignment
            else {
                continue;
            };
            let copy = matches!(result, E::Local { name: source } if scalars.contains(name)
                && length_target != Some(source));
            if !substitutable(name)
                || !(copy || (length_target.is_none() && is_movable_scalar_intrinsic(result)))
            {
                continue;
            }
            let Some(site) = definition.terminator_site else {
                continue;
            };
            let definition_site =
                definition
                    .statements
                    .iter()
                    .rev()
                    .find_map(|statement| match statement {
                        S::Site { site } => Some(*site),
                        _ => None,
                    });
            if definition_site != Some(site) {
                continue;
            }
            let value = match consumer
                .statements
                .iter_mut()
                .find(|statement| match statement {
                    S::Site { site: next } => *next != site,
                    S::BeginStorage { local } | S::EndStorage { local } => {
                        local != name && !removed.contains(local)
                    }
                    _ => true,
                }) {
                Some(S::Assign { value, .. }) => value,
                // The loop test can use its slice metadata directly, just
                // as it can use an unchanged copy of its index.
                None if (copy || matches!(result, E::SliceLength { .. }))
                    && consumer.terminator_site == Some(site) =>
                {
                    let T::If { condition, .. } = &mut consumer.terminator else {
                        continue;
                    };
                    condition
                }
                _ => continue,
            };
            if !straight_line_scalar(value) {
                continue;
            }
            let mut values = BTreeMap::from([(name.clone(), result.clone())]);
            let mut pending = Pending {
                values: &mut values,
                refused: Vec::new(),
            };
            substitute(value, &mut pending, true);
            if values.is_empty() {
                removed.insert(name.clone());
            }
        }
    }
}

/// The last scalar assignment can be the condition itself when its only
/// reader is the branch and no intervening marker changes its storage.
fn fold_scalar_condition(
    block: &mut MirBlock,
    substitutable: &impl Fn(&MirLocalId) -> bool,
    removed: &mut BTreeSet<MirLocalId>,
) {
    let T::If { condition, .. } = &mut block.terminator else {
        return;
    };
    // Charon emits a negated test when the switch lists the false case.
    let operand = match condition {
        E::Not { value } => value.as_mut(),
        condition => condition,
    };
    let E::Local { name: read } = operand else {
        return;
    };
    let Some(position) = block.statements.iter().rposition(|statement| {
        !matches!(
            statement,
            S::Site { .. } | S::BeginStorage { .. } | S::EndStorage { .. }
        )
    }) else {
        return;
    };
    let S::Assign {
        target: E::Local { name },
        value,
    } = &block.statements[position]
    else {
        return;
    };
    if read != name || !substitutable(name) || !straight_line_scalar(value) || checked(value) {
        return;
    }
    let mentioned = mentioned_locals(&block.statements[position]);
    if block.statements[position + 1..].iter().any(|statement| {
        matches!(statement, S::BeginStorage { local } | S::EndStorage { local }
            if mentioned.contains(local))
    }) {
        return;
    }
    *operand = value.clone();
    removed.insert(name.clone());
}

/// These expressions read an existing local and have no effect of their own.
fn is_movable_scalar_intrinsic(value: &E) -> bool {
    match value {
        E::SliceLength { slice } => matches!(
            slice.as_ref(),
            E::Borrow {
                place,
                value_type: Type::ByteSlice { mutable: false }
                    | Type::ScalarSlice { mutable: false, .. },
            } if matches!(place.as_ref(), E::Local { .. })
        ),
        E::IntegerFrom {
            value,
            source_type: Type::U8,
            value_type: Type::U32,
        } => {
            matches!(value.as_ref(), E::Local { .. })
        }
        _ => false,
    }
}

/// Moving a scalar intrinsic here cannot cross any effect, load, or
/// short-circuit branch within the consumer.
fn straight_line_scalar(value: &E) -> bool {
    match value {
        E::Binary {
            operator,
            left,
            right,
            ..
        } => {
            !matches!(operator.as_str(), "and" | "or")
                && straight_line_scalar(left)
                && straight_line_scalar(right)
        }
        E::Cast { value, .. } | E::IntegerFrom { value, .. } | E::Not { value } => {
            straight_line_scalar(value)
        }
        E::SliceLength { .. } => is_movable_scalar_intrinsic(value),
        E::Local { .. }
        | E::Integer { .. }
        | E::UnsignedInteger { .. }
        | E::SignedInteger { .. }
        | E::UsizeInteger { .. }
        | E::Boolean { .. } => true,
        _ => false,
    }
}

/// Put a remainder by a checked Rust constant back into the cast that
/// consumes it. The call to the constant initializer may panic, so it can
/// cross only storage markers that are already going away.
fn fold_constant_remainder_casts(
    statements: &mut [S],
    substitutable: &impl Fn(&MirLocalId) -> bool,
    constant_initializers: &BTreeSet<String>,
    removed: &mut BTreeSet<MirLocalId>,
) {
    let mut candidate: Option<(&mut MirLocalId, &mut E)> = None;
    for statement in statements {
        if let Some((name, remainder)) = candidate.take() {
            match statement {
                S::BeginStorage { local } | S::EndStorage { local } if removed.contains(local) => {
                    candidate = Some((name, remainder));
                    continue;
                }
                S::Assign {
                    value: E::Cast { value, .. },
                    ..
                } if matches!(value.as_ref(), E::Local { name: read } if read == name) => {
                    std::mem::swap(remainder, value.as_mut());
                    removed.insert(name.clone());
                    continue;
                }
                _ => {}
            }
        }
        if let S::Assign {
            target: E::Local { name },
            value,
        } = statement
            && let E::Binary {
                operator,
                left,
                right,
                ..
            } = value
            && operator == "rem"
            && matches!(left.as_ref(), E::Local { .. })
            && matches!(right.as_ref(), E::Call { function, arguments }
                if arguments.is_empty() && constant_initializers.contains(function))
            && substitutable(name)
        {
            candidate = Some((name, value));
        }
    }
}

/// The kind of iterator an iterator statement builds or moves.
#[derive(Clone, Copy, PartialEq, Eq)]
enum IteratorKind {
    SharedArray,
    Enumerate,
    Range,
    Chunk,
    /// A crate struct, built by `Initialize` or moved by `Move`, as `for` over
    /// `Countdown { n }` builds the iterator and moves it into the loop's.
    Record,
}

/// The iterator `statement` builds, as its kind and the local it builds.
fn iterator_definition(statement: &mut S) -> Option<(IteratorKind, &mut MirLocalId)> {
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
        S::Initialize { target, .. } | S::Move { target, .. } => {
            Some((IteratorKind::Record, target))
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
    temporaries: &BTreeSet<MirLocalId>,
    parameters: &BTreeMap<MirLocalId, super::super::schema::Type>,
) {
    substitute_invariant_values(locals, blocks, temporaries, parameters, None);
}

/// Bind a variant split to its unchanged source parameter once the earlier
/// passes have exposed the copy that feeds the split.
pub(super) fn bind_copied_enum_scrutinees(
    locals: &mut Vec<Place>,
    blocks: &mut [MirBlock],
    temporaries: &BTreeSet<MirLocalId>,
    parameters: &BTreeMap<MirLocalId, Type>,
) {
    if !parameters
        .values()
        .any(|ty| matches!(ty, Type::Enum { .. }))
    {
        return;
    }
    let scrutinees: BTreeSet<_> = blocks
        .iter()
        .filter_map(|block| enum_switch_local(&block.terminator))
        .filter(|name| temporaries.contains(*name))
        .cloned()
        .collect();
    if !scrutinees.is_empty() {
        substitute_invariant_values(locals, blocks, temporaries, parameters, Some(&scrutinees));
    }
}

fn substitute_invariant_values(
    locals: &mut Vec<Place>,
    blocks: &mut [MirBlock],
    temporaries: &BTreeSet<MirLocalId>,
    parameters: &BTreeMap<MirLocalId, Type>,
    enum_scrutinees: Option<&BTreeSet<MirLocalId>>,
) {
    let mut reads = BTreeMap::<MirLocalId, usize>::new();
    let mut named = BTreeSet::<MirLocalId>::new();
    let mut assignments = BTreeMap::<MirLocalId, Vec<E>>::new();
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
        if !enum_scrutinees.is_some_and(|scrutinees| {
            enum_switch_local(&block.terminator).is_some_and(|name| scrutinees.contains(name))
        }) {
            terminator_uses(&block.terminator, &mut reads, &mut named);
        }
        if let Some(destination) = call_destination(&block.terminator) {
            named.insert(destination.clone());
        }
    }
    let unchanged = unchanged_parameters(blocks, parameters);
    let types: BTreeMap<&MirLocalId, &super::super::schema::Type> = locals
        .iter()
        .map(|local| (&local.name, &local.value_type))
        .chain(parameters.iter())
        .collect();
    // Each temporary assigned once, by its one value.
    let candidates: BTreeMap<MirLocalId, E> = assignments
        .into_iter()
        .filter(|(name, values)| {
            temporaries.contains(name) && !named.contains(name) && values.len() == 1
        })
        // A variant split needs a binding. Only replace its copy with an
        // unchanged source parameter of the same enum type.
        .filter(|(name, values)| {
            enum_scrutinees.is_none_or(|scrutinees| {
                scrutinees.contains(name)
                    && matches!(values.as_slice(), [E::Local { name: source }]
                    if unchanged.contains(source)
                        && matches!(types.get(name), Some(Type::Enum { .. }))
                        && types.get(name).copied() == parameters.get(source))
            })
        })
        .filter_map(|(name, mut values)| Some((name, values.pop()?)))
        .collect();
    // A candidate's value with the unchanging candidates it reads put back,
    // or `None` when it changes. A reborrow `t = &mut *u` of `u = &mut x` is
    // `&mut x`, so a chain of borrows resolves link by link, each once.
    let mut resolved = BTreeMap::<MirLocalId, Option<E>>::new();
    let names: Vec<MirLocalId> = candidates.keys().cloned().collect();
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
    let literals: BTreeMap<MirLocalId, E> = resolved
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
fn put_back(expression: &mut E, values: &BTreeMap<MirLocalId, E>) {
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
    name: &MirLocalId,
    candidates: &BTreeMap<MirLocalId, E>,
    unchanged: &BTreeSet<MirLocalId>,
    types: &BTreeMap<&MirLocalId, &super::super::schema::Type>,
    resolved: &mut BTreeMap<MirLocalId, Option<E>>,
    visiting: &mut BTreeSet<MirLocalId>,
) -> Option<E> {
    if let Some(value) = resolved.get(name) {
        return value.clone();
    }
    let value = candidates.get(name)?;
    if !visiting.insert(name.clone()) {
        return None;
    }
    // Every local the value reads, including a slice a length takes apart.
    fn locals_in(expression: &E, out: &mut BTreeSet<MirLocalId>) {
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
    let temporary_type = types.get(name).copied();
    // A reborrow of an unchanged record reference carries the same object
    // through the call. The original parameter can name that reference.
    if let E::Borrow { place, value_type } = &value
        && let E::Deref {
            reference,
            value_type: record @ Type::Record { .. },
        } = place.as_ref()
        && matches!(value_type, Type::Reference { pointee, .. } if pointee.as_ref() == record)
        && let E::Local { name: source } = reference.as_ref()
        && temporary_type == Some(value_type)
        && types.get(source).copied() == Some(value_type)
        && unchanged.contains(source)
    {
        value = reference.as_ref().clone();
    }
    let unchanging = match &value {
        E::Borrow { place, value_type } => match temporary_type {
            Some(Type::Reference { .. }) => {
                place_root(place).is_some()
                    || matches!(place.as_ref(), E::Field { base, .. }
                        if matches!(base.as_ref(), E::Deref { reference, value_type: Type::Record { .. } }
                            if matches!(reference.as_ref(), E::Local { name } if unchanged.contains(name))))
            }
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
        // A shared slice of a local array, `&words[..]`: the array's address
        // and length never change while the slice lives.
        E::ArrayToSlice {
            array,
            mutable: false,
        } => {
            matches!(
                temporary_type,
                Some(
                    super::super::schema::Type::ByteSlice { mutable: false }
                        | super::super::schema::Type::ScalarSlice { mutable: false, .. }
                )
            ) && match array.as_ref() {
                E::Borrow { place, .. } => place_root(place).is_some(),
                _ => false,
            }
        }
        value => unchanging_scalar(value, unchanged),
    };
    let result = unchanging.then_some(value);
    resolved.insert(name.clone(), result.clone());
    result
}

/// Whether `value` is the same wherever it is read: a literal, an
/// `unchanged` parameter, or the length or a conversion of one.
fn unchanging_scalar(value: &E, unchanged: &BTreeSet<MirLocalId>) -> bool {
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
    parameters: &BTreeMap<MirLocalId, super::super::schema::Type>,
) -> BTreeSet<MirLocalId> {
    // The local a target writes, unless it writes through a reference.
    fn written(target: &E) -> Option<&MirLocalId> {
        match target {
            E::Local { name } => Some(name),
            E::Field { base, .. } | E::EnumField { base, .. } => written(base),
            E::Index { slice, .. } => written(slice),
            _ => None,
        }
    }
    // A shared borrow of a reference or a slice cannot change it: the
    // variable holds an address and a length, with no interior mutability.
    let pointer_like = |name: &MirLocalId| {
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
        out: &mut BTreeSet<MirLocalId>,
        pointer_like: &dyn Fn(&MirLocalId) -> bool,
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
        if let T::Call {
            destination: Some(destination),
            ..
        } = &block.terminator
        {
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
    temporaries: &BTreeSet<MirLocalId>,
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
        if let T::Call {
            destination: Some(destination),
            ..
        } = &block.terminator
        {
            used.insert(destination.clone());
        }
    }
    // A `()` call result holds nothing, so being a destination is no use.
    let unit: BTreeSet<&MirLocalId> = locals
        .iter()
        .filter(|local| local.value_type == super::super::schema::Type::Unit)
        .map(|local| &local.name)
        .collect();
    let unused: BTreeSet<MirLocalId> = locals
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
fn only_destination(blocks: &[MirBlock], name: &MirLocalId) -> bool {
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

/// A length-only read of a shared slice can use its original value. Keep the
/// copy if the slice could change before the return or if anything else reads it.
pub(super) fn fold_returned_slice_lengths(
    locals: &mut Vec<Place>,
    blocks: &mut [MirBlock],
    temporaries: &BTreeSet<MirLocalId>,
) {
    let slices: BTreeSet<_> = locals
        .iter()
        .filter(|local| {
            local.value_type == (Type::ByteSlice { mutable: false })
                && temporaries.contains(&local.name)
        })
        .map(|local| &local.name)
        .collect();
    if slices.is_empty() {
        return;
    }
    let mut predecessors = vec![0usize; blocks.len()];
    for block in blocks.iter() {
        for target in successors(&block.terminator) {
            if let Some(count) = predecessors.get_mut(target) {
                *count += 1;
            }
        }
    }
    let mut folds = Vec::new();
    for (index, block) in blocks.iter().enumerate() {
        let continuation = match &block.terminator {
            T::ReturnValue { .. } => index,
            T::Goto { target }
                if *target != 0
                    && *target != index
                    && predecessors.get(*target) == Some(&1)
                    && blocks[*target]
                        .statements
                        .iter()
                        .all(|s| matches!(s, S::Site { .. })) =>
            {
                *target
            }
            _ => continue,
        };
        let T::ReturnValue {
            value: E::SliceLength { slice },
        } = &blocks[continuation].terminator
        else {
            continue;
        };
        let operand = match slice.as_ref() {
            E::Borrow {
                place,
                value_type: Type::ByteSlice { mutable: false },
            } => place.as_ref(),
            operand => operand,
        };
        let E::Local { name } = operand else { continue };
        if !slices.contains(name) {
            continue;
        }
        if let Some(S::Assign {
            target: E::Local { name: destination },
            value,
        }) = block
            .statements
            .iter()
            .rfind(|statement| !matches!(statement, S::Site { .. }))
            && destination == name
            && match value {
                E::Local { name: source } | E::ChunkRemainder { iterator: source } => {
                    source != name
                }
                E::ArrayToSlice {
                    array,
                    mutable: false,
                } => array_coercion_root(array).is_some_and(|root| root != name),
                _ => false,
            }
        {
            folds.push((continuation, name.clone(), value.clone()));
        }
    }
    if folds.is_empty() {
        return;
    }
    let mut mentions = BTreeMap::<MirLocalId, usize>::new();
    for block in blocks.iter() {
        for statement in &block.statements {
            for name in mentioned_locals(statement) {
                *mentions.entry(name).or_default() += 1;
            }
        }
        let mut reads = BTreeMap::new();
        let mut named = BTreeSet::new();
        terminator_uses(&block.terminator, &mut reads, &mut named);
        named.extend(reads.into_keys());
        named.extend(call_destination(&block.terminator).cloned());
        for name in named {
            *mentions.entry(name).or_default() += 1;
        }
    }
    let mut removed = BTreeSet::new();
    for (continuation, name, value) in folds {
        if mentions.get(&name) == Some(&2)
            && let T::ReturnValue {
                value: E::SliceLength { slice },
            } = &mut blocks[continuation].terminator
        {
            **slice = value;
            removed.insert(name);
        }
    }
    for block in blocks {
        block.statements.retain(|statement| match statement {
            S::Assign {
                target: E::Local { name },
                ..
            } => !removed.contains(name),
            S::BeginStorage { local } | S::EndStorage { local } => !removed.contains(local),
            _ => true,
        });
    }
    locals.retain(|local| !removed.contains(&local.name));
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
pub(super) fn return_values(
    locals: &mut Vec<Place>,
    blocks: &mut [MirBlock],
    return_place: &MirLocalId,
) {
    let Some(place) = locals.iter().find(|local| &local.name == return_place) else {
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
            // The return reads the value where the write did: the storage
            // ends between them, which the return performs anyway, would
            // otherwise end a local the value reads first.
            let tail = blocks[block].statements.split_off(position);
            blocks[block].statements.extend(
                tail.into_iter()
                    .filter(|statement| !matches!(statement, S::EndStorage { .. })),
            );
            blocks[block].terminator = T::ReturnValue { value };
        }
        None => {
            let T::Call {
                function, target, ..
            } = &blocks[block].terminator
            else {
                unreachable!("the return place's writer is a call")
            };
            // A call through a pointer assigns its destination; it is no step.
            if matches!(function, MirCallee::Pointer { .. }) {
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
            if let T::Call {
                destination,
                result,
                ..
            } = &mut blocks[block].terminator
            {
                *destination = None;
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
    locals.retain(|local| &local.name != return_place);
}

/// Whether a value of `value_type` is returned as a value without address-backed return storage.
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
            | Type::Vec { .. }
    )
}

/// What a split `next` of a slice, enumerated slice or chunk iterator
/// yields into its `Some` arm, read from its `Option`.
#[derive(Clone, Copy, PartialEq)]
enum Yielded {
    /// The element's reference, `SharedArrayOptionElement`.
    Element,
    /// An enumeration's index, `EnumerateOptionIndex`.
    Index,
    /// A chunk, `ChunkOptionSlice`.
    Chunk,
}

/// The `Option` a split `next` builds, whether its `for` header decided it
/// yields, and what its `Some` arm may read: the element of a slice
/// iterator, the index and element of an enumeration, the chunk of a chunk
/// iterator.
fn split_next(statement: &S) -> Option<(&MirLocalId, Option<bool>, &'static [Yielded])> {
    match statement {
        S::SharedArrayNext {
            option: Some(option),
            taken,
            ..
        } => Some((option, *taken, &[Yielded::Element])),
        S::EnumerateNext {
            option: Some(option),
            taken,
            ..
        } => Some((option, *taken, &[Yielded::Index, Yielded::Element])),
        S::ChunkNext {
            option: Some(option),
            taken,
            ..
        } => Some((option, *taken, &[Yielded::Chunk])),
        _ => None,
    }
}

/// What `value` reads from `option`, when it reads one yielded value.
fn yielded_read(value: &E, option: &MirLocalId) -> Option<Yielded> {
    match value {
        E::SharedArrayOptionElement { option: read } if read == option => Some(Yielded::Element),
        E::EnumerateOptionIndex { option: read } if read == option => Some(Yielded::Index),
        E::ChunkOptionSlice { option: read } if read == option => Some(Yielded::Chunk),
        _ => None,
    }
}

/// Binds a slice, enumerated slice or chunk loop's variables where `next`
/// yields, as [`bind_range_payloads`] does for a range: once the protocol has
/// split `next` into its two outcomes, the `Option` it returns is read only
/// by the `Some` arm's first statements, `x = (opt as Some).0`, and by the
/// tag test the split left unreachable. The yielding outcome then assigns
/// those locals itself (`payload`, or an enumeration's `index` and
/// `element`), or only moves on when the arm binds nothing (`Some(_)`); the
/// other outcome is nothing; and the `Option`, its tag test and its
/// temporary go.
pub(super) fn bind_slice_payloads(
    locals: &mut Vec<Place>,
    blocks: &mut [MirBlock],
    temporaries: &BTreeSet<MirLocalId>,
) {
    let transparent = |statement: &S| {
        matches!(
            statement,
            S::BeginStorage { .. } | S::EndStorage { .. } | S::Site { .. }
        )
    };
    // A block that tests the `Option`'s tag, which the split replaced.
    let tests = |block: &MirBlock, option: &MirLocalId| {
        matches!(
            &block.terminator,
            T::If {
                condition: E::SharedArrayOptionTag { option: tested }
                    | E::ChunkOptionTag { option: tested },
                ..
            } if tested == option
        )
    };
    let tag_copy = |statement: &S, option: &MirLocalId| {
        matches!(
            statement,
            S::Assign {
                value: E::SharedArrayOptionTag { option: tag } | E::ChunkOptionTag { option: tag },
                ..
            } if tag == option
        )
    };
    let mut removed = BTreeSet::new();
    for index in 0..blocks.len() {
        let (option, yields, target) = match (
            blocks[index].statements.last().and_then(split_next),
            &blocks[index].terminator,
        ) {
            (Some((option, Some(true), yields)), T::Goto { target }) => {
                (option.clone(), yields, *target)
            }
            _ => continue,
        };
        if !temporaries.contains(&option) || removed.contains(&option) {
            continue;
        }
        // The `Some` arm's leading bindings of what it yields, `x = (opt as
        // Some).0`, each at most once; a `Some(_)` arm binds nothing.
        let mut bindings = Vec::<(usize, Yielded, MirLocalId)>::new();
        for (position, statement) in blocks[target].statements.iter().enumerate() {
            if transparent(statement) {
                continue;
            }
            match statement {
                S::Assign {
                    target: E::Local { name },
                    value,
                } => match yielded_read(value, &option) {
                    Some(read)
                        if yields.contains(&read)
                            && !bindings.iter().any(|(_, bound, _)| *bound == read) =>
                    {
                        bindings.push((position, read, name.clone()));
                    }
                    _ => break,
                },
                _ => break,
            }
        }
        // Nothing else names the `Option`: its `next` outcomes, each decided,
        // the bindings, and the replaced tag test and its tag copies.
        let mut nexts = 0;
        let mut others = 0;
        for (number, block) in blocks.iter().enumerate() {
            let replaced = tests(block, &option);
            for (place, statement) in block.statements.iter().enumerate() {
                if transparent(statement) || !mentioned_locals(statement).contains(&option) {
                    continue;
                }
                if split_next(statement).is_some_and(|(_, taken, _)| taken.is_some()) {
                    nexts += 1;
                } else if (replaced && tag_copy(statement, &option))
                    || (number == target
                        && bindings.iter().any(|(position, _, _)| *position == place))
                {
                } else {
                    others += 1;
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
        for (position, _, _) in bindings.iter().rev() {
            blocks[target].statements.remove(*position);
        }
        start_storage_at_next(
            blocks,
            index,
            target,
            bindings.iter().map(|(_, _, name)| name),
        );
        let bound = |read: Yielded| {
            bindings
                .iter()
                .find(|(_, bound, _)| *bound == read)
                .map(|(_, _, name)| name.clone())
        };
        for block in blocks.iter_mut() {
            if tests(block, &option) {
                block
                    .statements
                    .retain(|statement| !tag_copy(statement, &option));
                block.terminator = T::Unreachable;
            }
            for statement in &mut block.statements {
                if !split_next(statement).is_some_and(|(next_option, _, _)| *next_option == option)
                {
                    continue;
                }
                match statement {
                    S::SharedArrayNext {
                        option: next_option,
                        payload,
                        taken,
                        ..
                    } => {
                        *next_option = None;
                        if *taken == Some(true) {
                            *payload = bound(Yielded::Element);
                        }
                    }
                    S::EnumerateNext {
                        option: next_option,
                        index,
                        element,
                        taken,
                        ..
                    } => {
                        *next_option = None;
                        if *taken == Some(true) {
                            *index = bound(Yielded::Index);
                            *element = bound(Yielded::Element);
                        }
                    }
                    S::ChunkNext {
                        option: next_option,
                        payload,
                        taken,
                        ..
                    } => {
                        *next_option = None;
                        if *taken == Some(true) {
                            *payload = bound(Yielded::Chunk);
                        }
                    }
                    _ => {}
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

/// The original iterator and reference binding, plus an enumeration's
/// separate index binding if it yields one.
fn copied_element_yield(statement: &S) -> Option<(&MirLocalId, &MirLocalId, Option<&MirLocalId>)> {
    match statement {
        S::SharedArrayNext {
            iterator,
            option: None,
            payload: Some(reference),
            taken: Some(true),
        } => Some((iterator, reference, None)),
        S::EnumerateNext {
            iterator,
            option: None,
            index,
            element: Some(reference),
            taken: Some(true),
        } => Some((iterator, reference, index.as_ref())),
        _ => None,
    }
}

/// Bind a copied slice element to the written pattern variable. The yielded
/// shared reference can go when its only use is the matching dereference at
/// the start of the sole successor, under the same source site.
pub(super) fn bind_copied_slice_elements(
    locals: &mut Vec<Place>,
    blocks: &mut [MirBlock],
    temporaries: &BTreeSet<MirLocalId>,
) {
    let types: BTreeMap<_, _> = locals
        .iter()
        .map(|local| (&local.name, &local.value_type))
        .collect();
    let mut reads = BTreeMap::new();
    let mut named = BTreeSet::new();
    let mut yields = BTreeMap::<MirLocalId, usize>::new();
    let mut predecessors = vec![0usize; blocks.len()];
    for block in blocks.iter() {
        for statement in &block.statements {
            if let Some((iterator, reference, index)) = copied_element_yield(statement) {
                *yields.entry(reference.clone()).or_default() += 1;
                named.insert(iterator.clone());
                named.extend(index.cloned());
            } else {
                statement_uses(statement, &mut reads, &mut named);
                if let S::Assign {
                    target: E::Local { name },
                    ..
                } = statement
                {
                    named.insert(name.clone());
                }
            }
        }
        terminator_uses(&block.terminator, &mut reads, &mut named);
        if let Some(name) = call_destination(&block.terminator) {
            named.insert(name.clone());
        }
        for successor in successors(&block.terminator) {
            if let Some(count) = predecessors.get_mut(successor) {
                *count += 1;
            }
        }
    }
    let mut removed = BTreeSet::new();
    for index in 0..blocks.len() {
        let (Some((iterator, reference, _)), T::Goto { target }) = (
            blocks[index]
                .statements
                .last()
                .and_then(copied_element_yield),
            &blocks[index].terminator,
        ) else {
            continue;
        };
        let target = *target;
        if target == 0
            || target == index
            || predecessors.get(target) != Some(&1)
            || !temporaries.contains(reference)
            || reads.get(reference) != Some(&1)
            || yields.get(reference) != Some(&1)
            || named.contains(reference)
        {
            continue;
        }
        let Some(Type::SharedArrayIterator { element } | Type::EnumerateIterator { element }) =
            types.get(iterator)
        else {
            continue;
        };
        if !element.is_integer()
            || !matches!(types.get(reference),
                Some(Type::Reference { mutable: false, pointee }) if pointee == element)
        {
            continue;
        }
        let Some(site) = blocks[index].terminator_site else {
            continue;
        };
        if blocks[index]
            .statements
            .iter()
            .rev()
            .find_map(|statement| match statement {
                S::Site { site } => Some(*site),
                _ => None,
            })
            != Some(site)
        {
            continue;
        }
        let Some((
            position,
            S::Assign {
                target: E::Local { name },
                value:
                    E::Deref {
                        reference: input,
                        value_type,
                    },
            },
        )) = blocks[target]
            .statements
            .iter()
            .enumerate()
            .find(|(_, statement)| {
                !matches!(statement, S::Site { site: next } if *next == site)
                    && !matches!(statement, S::BeginStorage { .. })
            })
        else {
            continue;
        };
        let prefix = &blocks[target].statements[..position];
        if temporaries.contains(name)
            || *value_type != **element
            || types.get(name) != Some(&value_type)
            || !matches!(input.as_ref(), E::Local { name: read } if read == reference)
            || !prefix
                .iter()
                .any(|statement| matches!(statement, S::Site { site: next } if *next == site))
            || prefix
                .iter()
                .any(|statement| matches!(statement, S::BeginStorage { local } if local != name))
        {
            continue;
        }
        let (reference, name) = (reference.clone(), name.clone());
        blocks[target].statements.remove(position);
        start_storage_at_next(blocks, index, target, [&name]);
        match blocks[index].statements.last_mut() {
            Some(S::SharedArrayNext { payload, .. })
            | Some(S::EnumerateNext {
                element: payload, ..
            }) => *payload = Some(name),
            _ => unreachable!("yield remains the last statement"),
        }
        removed.insert(reference);
    }
    if removed.is_empty() {
        return;
    }
    for block in blocks {
        block.statements.retain(|statement| match statement {
            S::BeginStorage { local } | S::EndStorage { local } => !removed.contains(local),
            _ => true,
        });
    }
    locals.retain(|local| !removed.contains(&local.name));
}

/// Bind the two parts of a split directly when the only use of each
/// anonymous component is a copy to its destination in the same source
/// statement. Keep the tuple storage when either component also escapes.
pub(super) fn bind_split_slice_results(
    locals: &mut Vec<Place>,
    blocks: &mut [MirBlock],
    anonymous_components: &BTreeSet<MirLocalId>,
) {
    if anonymous_components.is_empty() {
        return;
    }
    let slices: BTreeSet<_> = locals
        .iter()
        .filter(|local| local.value_type == (Type::ByteSlice { mutable: false }))
        .map(|local| &local.name)
        .collect();
    let mut reads = BTreeMap::new();
    let mut named = BTreeSet::new();
    let mut splits = BTreeMap::<MirLocalId, usize>::new();
    let mut predecessors = vec![0; blocks.len()];
    for block in blocks.iter() {
        for statement in &block.statements {
            if let S::SliceSplit {
                slice,
                midpoint,
                left,
                right,
            } = statement
            {
                expression_uses(slice, &mut reads, &mut named);
                expression_uses(midpoint, &mut reads, &mut named);
                for output in [left, right] {
                    *splits.entry(output.clone()).or_default() += 1;
                }
            } else {
                statement_uses(statement, &mut reads, &mut named);
                if let S::Assign {
                    target: E::Local { name },
                    ..
                } = statement
                {
                    named.insert(name.clone());
                }
            }
        }
        // Count other writes and uses separately from the split's outputs.
        terminator_uses(&block.terminator, &mut reads, &mut named);
        if let Some(destination) = call_destination(&block.terminator) {
            named.insert(destination.clone());
        }
        for successor in successors(&block.terminator) {
            if let Some(count) = predecessors.get_mut(successor) {
                *count += 1;
            }
        }
    }
    let mut removed = BTreeSet::new();
    for index in 0..blocks.len() {
        let T::Goto { target } = blocks[index].terminator else {
            continue;
        };
        if target == 0 || predecessors.get(target) != Some(&1) {
            continue;
        }
        let Ok([definition, consumer]) = blocks.get_disjoint_mut([index, target]) else {
            continue;
        };
        let Some(site) = definition.terminator_site else {
            continue;
        };
        let definition_site =
            definition
                .statements
                .iter()
                .rev()
                .find_map(|statement| match statement {
                    S::Site { site } => Some(*site),
                    _ => None,
                });
        if definition_site != Some(site)
            || !matches!(consumer.statements.first(), Some(S::Site { site: entry }) if *entry == site)
        {
            continue;
        }
        let Some(S::SliceSplit { left, right, .. }) = definition.statements.last() else {
            continue;
        };
        if left == right
            || [left, right].into_iter().any(|output| {
                !anonymous_components.contains(output)
                    || reads.get(output) != Some(&1)
                    || splits.get(output) != Some(&1)
                    || named.contains(output)
            })
        {
            continue;
        }
        let mut effects = consumer
            .statements
            .iter()
            .enumerate()
            .filter(|(_, statement)| {
                !matches!(statement, S::Site { site: next } if *next == site)
                    && !matches!(statement, S::BeginStorage { .. })
            });
        let mut take_copy = |output: &MirLocalId| {
            let (
                position,
                S::Assign {
                    target: E::Local { name: destination },
                    value: E::Local { name: source },
                },
            ) = effects.next()?
            else {
                return None;
            };
            (source == output
                && slices.contains(destination)
                && !anonymous_components.contains(destination))
            .then_some((position, destination.clone()))
        };
        let (Some((first, left_destination)), Some((last, right_destination))) =
            (take_copy(left), take_copy(right))
        else {
            continue;
        };
        if left_destination == right_destination
            || consumer.statements[..last].iter().any(|statement| {
                matches!(statement, S::BeginStorage { local }
                    if local != &left_destination && local != &right_destination)
            })
        {
            continue;
        }
        removed.extend([left.clone(), right.clone()]);
        let mut starts = Vec::new();
        let mut position = 0;
        consumer.statements.retain(|statement| {
            let keep = if position == first || position == last {
                false
            } else if position < last && matches!(statement, S::BeginStorage { .. }) {
                starts.push(statement.clone());
                false
            } else {
                true
            };
            position += 1;
            keep
        });
        let Some(S::SliceSplit { left, right, .. }) = definition.statements.last_mut() else {
            unreachable!("split remains the last statement");
        };
        *left = left_destination;
        *right = right_destination;
        let before_split = definition.statements.len() - 1;
        definition
            .statements
            .splice(before_split..before_split, starts);
    }
    if !removed.is_empty() {
        for block in blocks {
            block.statements.retain(|statement| {
                !matches!(statement, S::BeginStorage { local } | S::EndStorage { local }
                    if removed.contains(local))
            });
        }
        locals.retain(|local| !removed.contains(&local.name));
    }
}

/// Starts the storage of the locals the taken `next` ending block `next`
/// now binds there, rather than in the `Some` arm `arm` that bound them: a
/// binding's storage starts before its first write. Only the arm's leading
/// storage markers move; the block holding the taken `next` leads only to
/// the arm.
fn start_storage_at_next<'a>(
    blocks: &mut [MirBlock],
    next: usize,
    arm: usize,
    bound: impl IntoIterator<Item = &'a MirLocalId>,
) {
    for name in bound {
        let Some(position) = blocks[arm]
            .statements
            .iter()
            .take_while(|statement| {
                matches!(
                    statement,
                    S::BeginStorage { .. } | S::EndStorage { .. } | S::Site { .. }
                )
            })
            .position(|statement| matches!(statement, S::BeginStorage { local } if local == name))
        else {
            continue;
        };
        let start = blocks[arm].statements.remove(position);
        let at = blocks[next].statements.len() - 1;
        blocks[next].statements.insert(at, start);
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
    temporaries: &BTreeSet<MirLocalId>,
) {
    let mut mentions = BTreeMap::<MirLocalId, usize>::new();
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
        start_storage_at_next(blocks, index, target, [&payload]);
        for block in blocks.iter_mut() {
            for statement in &mut block.statements {
                if let S::RangeNext {
                    option: next_option,
                    payload: next_payload,
                    taken,
                    ..
                } = statement
                    && next_option.as_ref() == Some(&option)
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

fn iterator_move(statement: &S) -> Option<(IteratorKind, &MirLocalId, &MirLocalId)> {
    match statement {
        S::SharedArrayMove { target, source } => Some((IteratorKind::SharedArray, target, source)),
        S::EnumerateMove { target, source } => Some((IteratorKind::Enumerate, target, source)),
        S::RangeMove { target, source } => Some((IteratorKind::Range, target, source)),
        S::ChunkMove { target, source } => Some((IteratorKind::Chunk, target, source)),
        S::Move { target, source, .. } => Some((IteratorKind::Record, target, source)),
        _ => None,
    }
}

/// Builds each iterator in the local the program moves it into. MIR builds
/// a `for` loop's iterator in a temporary and moves it, sometimes twice,
/// into the loop's own: `t1 = 0..n; t2 = t1; iter = t2` is `iter = 0..n`.
/// A move from a temporary that nothing else names, whose definition comes
/// just before it, past nothing but storage markers and source sites, takes
/// that definition's place, and the temporary is gone. The definition may
/// end a block that only jumps to the move's. A crate struct moves the same
/// way: `t2 = Countdown { n }; t1 = t2; iter = t1` is `iter = Countdown { n }`.
pub(super) fn collapse_iterator_moves(
    locals: &mut Vec<Place>,
    blocks: &mut [MirBlock],
    temporaries: &BTreeSet<MirLocalId>,
) {
    let mut mentions = BTreeMap::<MirLocalId, usize>::new();
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
                    | IteratorKind::Record
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

/// A source drop that moves its argument into a fresh, addressable place.
pub(in crate::languages::rust) fn moved_drop_operands(mir: &MirBody) -> BTreeMap<&MirLocalId, u32> {
    let mut candidates = BTreeMap::new();
    let mut sites = BTreeMap::<u32, usize>::new();
    for block in &mir.blocks {
        let (T::Drop { local, record, .. }, Some(site)) =
            (&block.terminator, block.terminator_site)
        else {
            continue;
        };
        *sites.entry(site).or_default() += 1;
        if mir.unnamed_locals.contains(local)
            && let Some(S::Move {
                target,
                source,
                record: moved,
            }) = block
                .statements
                .iter()
                .rev()
                .find(|statement| !matches!(statement, S::Site { .. }))
            && target == local
            && source != local
            && moved == record
        {
            candidates.insert(local, (site, 0usize));
        }
    }
    if candidates.is_empty() {
        return BTreeMap::new();
    }
    for block in &mir.blocks {
        for statement in &block.statements {
            for name in mentioned_locals(statement) {
                if let Some((_, mentions)) = candidates.get_mut(&name) {
                    *mentions += 1;
                }
            }
        }
        let mut reads = BTreeMap::new();
        let mut named = BTreeSet::new();
        terminator_uses(&block.terminator, &mut reads, &mut named);
        named.extend(reads.into_keys());
        named.extend(call_destination(&block.terminator).cloned());
        for name in named {
            if let Some((_, mentions)) = candidates.get_mut(&name) {
                *mentions += 1;
            }
        }
    }
    candidates
        .into_iter()
        .filter_map(|(local, (site, mentions))| {
            (mentions == 2 && sites[&site] == 1).then_some((local, site))
        })
        .collect()
}

/// Pass an adjacent by-value copy directly to the call that takes it. The
/// callee already gets its own copy, so no caller-side storage is needed.
pub(super) fn bind_copied_call_arguments(
    locals: &mut Vec<Place>,
    blocks: &mut [MirBlock],
    temporaries: &BTreeSet<MirLocalId>,
) {
    let mut copies = Vec::new();
    for (block_index, block) in blocks.iter().enumerate() {
        let T::Call {
            owned_arguments,
            arguments,
            ..
        } = &block.terminator
        else {
            continue;
        };
        let Some(argument) = owned_arguments.last() else {
            continue;
        };
        let Some(local) = &argument.local else {
            continue;
        };
        if !argument.moved
            || argument.index.checked_add(1) != Some(arguments.len())
            || call_destination(&block.terminator) == Some(local)
            || !temporaries.contains(local)
        {
            continue;
        }
        let Some((
            position,
            S::Copy {
                target,
                source,
                record,
            },
        )) = block.statements.iter().enumerate().rev().find(|(_, code)| {
            !matches!(
                code,
                S::Site { .. } | S::BeginStorage { .. } | S::EndStorage { .. }
            )
        })
        else {
            continue;
        };
        if target != local
            || record != &argument.record
            || target == source
            || !matches!(arguments.last(), Some(E::Local { name }) if name == target)
        {
            continue;
        }
        if block.statements[position + 1..].iter().any(|code| {
            matches!(code, S::BeginStorage { local } | S::EndStorage { local } if local == source)
        }) {
            continue;
        }
        // The call may prepare earlier arguments. Any nested call can write
        // the source, so the copy needs to stay at its original point.
        if arguments[..argument.index]
            .iter()
            .any(|argument| contains_call(argument) || mentioned_in_expression(argument, target))
        {
            continue;
        }
        copies.push((block_index, position, target.clone(), source.clone()));
    }
    if copies.is_empty() {
        return;
    }

    let mut mentions: BTreeMap<_, usize> = copies
        .iter()
        .map(|(_, _, target, _)| (target.clone(), 0))
        .collect();
    for block in blocks.iter() {
        for statement in &block.statements {
            for key in mentioned_locals(statement) {
                if let Some(count) = mentions.get_mut(&key) {
                    *count += 1;
                }
            }
        }
        let mut reads = BTreeMap::new();
        let mut named = BTreeSet::new();
        terminator_uses(&block.terminator, &mut reads, &mut named);
        named.extend(reads.into_keys());
        named.extend(call_destination(&block.terminator).cloned());
        for key in named {
            if let Some(count) = mentions.get_mut(&key) {
                *count += 1;
            }
        }
    }

    let mut removed = BTreeSet::new();
    for (block, position, target, source) in copies {
        if mentions[&target] != 2 {
            continue;
        }
        let block = &mut blocks[block];
        let T::Call {
            owned_arguments,
            arguments,
            ..
        } = &mut block.terminator
        else {
            unreachable!("selected from a call block");
        };
        let argument = owned_arguments
            .last_mut()
            .expect("selected a copied argument");
        *arguments.last_mut().expect("selected a copied argument") = E::Local {
            name: source.clone(),
        };
        argument.local = Some(source);
        argument.moved = false;
        block.statements.remove(position);
        removed.insert(target);
    }
    for block in blocks.iter_mut() {
        block.statements.retain(|statement| match statement {
            S::BeginStorage { local } | S::EndStorage { local } => !removed.contains(local),
            _ => true,
        });
    }
    locals.retain(|local| !removed.contains(&local.name));
}

fn contains_call(expression: &E) -> bool {
    matches!(expression, E::Call { .. } | E::ClosureInstance { .. })
        || children(expression).into_iter().any(contains_call)
}

fn mentioned_in_expression(expression: &E, local: &MirLocalId) -> bool {
    let mut reads = BTreeMap::new();
    let mut named = BTreeSet::new();
    expression_uses(expression, &mut reads, &mut named);
    reads.contains_key(local) || named.contains(local)
}

/// Call an unchanged callback parameter directly when MIR only copied it to
/// name the callee. In particular, the parameter cannot change while a call
/// in an argument runs, because nothing writes it or takes its address.
pub(super) fn fold_callback_copies(
    locals: &mut Vec<Place>,
    blocks: &mut [MirBlock],
    temporaries: &BTreeSet<MirLocalId>,
    parameters: &BTreeMap<MirLocalId, Type>,
) {
    if !parameters
        .values()
        .any(|ty| matches!(ty, Type::FnPointer { .. }))
    {
        return;
    }
    let mut reads = BTreeMap::new();
    let mut named = BTreeSet::new();
    let mut writes = BTreeMap::<MirLocalId, usize>::new();
    let mut copies = BTreeMap::new();
    let mut callees = BTreeMap::<MirLocalId, usize>::new();
    let mut predecessors = vec![(None, 0usize); blocks.len()];
    for (index, block) in blocks.iter().enumerate() {
        for statement in &block.statements {
            statement_uses(statement, &mut reads, &mut named);
            match statement {
                S::Assign {
                    target: E::Local { name },
                    value,
                } => {
                    *writes.entry(name.clone()).or_default() += 1;
                    if let E::Local { name: source } = value
                        && temporaries.contains(name)
                        && matches!(parameters.get(source), Some(Type::FnPointer { .. }))
                    {
                        copies.insert(name.clone(), (index, source.clone()));
                    }
                }
                S::BeginStorage { local } | S::EndStorage { local }
                    if parameters.contains_key(local) =>
                {
                    named.insert(local.clone());
                }
                _ => {}
            }
        }
        if let T::Call {
            function: MirCallee::Pointer { local: function },
            arguments,
            owned_arguments,
            ..
        } = &block.terminator
        {
            *callees.entry(function.clone()).or_default() += 1;
            for argument in arguments {
                expression_uses(argument, &mut reads, &mut named);
            }
            named.extend(
                owned_arguments
                    .iter()
                    .filter_map(|argument| argument.local.clone()),
            );
        } else {
            terminator_uses(&block.terminator, &mut reads, &mut named);
        }
        if let Some(destination) = call_destination(&block.terminator) {
            *writes.entry(destination.clone()).or_default() += 1;
        }
        for target in successors(&block.terminator) {
            if let Some((predecessor, count)) = predecessors.get_mut(target) {
                *predecessor = Some(index);
                *count += 1;
            }
        }
    }

    let types: BTreeMap<_, _> = locals
        .iter()
        .map(|local| (&local.name, &local.value_type))
        .collect();
    let mut removed = BTreeSet::new();
    for (index, block) in blocks.iter_mut().enumerate() {
        let T::Call {
            function: MirCallee::Pointer { local: function },
            ..
        } = &mut block.terminator
        else {
            continue;
        };
        let Some((producer, source)) = copies.get(function) else {
            continue;
        };
        if writes.get(function) == Some(&1)
            && callees.get(function) == Some(&1)
            && !reads.contains_key(function)
            && !named.contains(function)
            && !writes.contains_key(source)
            && !named.contains(source)
            && types.get(function).copied() == parameters.get(source)
            && (*producer == index
                || (*producer < index && predecessors[index] == (Some(*producer), 1)))
        {
            removed.insert(std::mem::replace(function, source.clone()));
        }
    }
    for block in blocks {
        block.statements.retain(|statement| match statement {
            S::Assign {
                target: E::Local { name },
                ..
            } => !removed.contains(name),
            S::BeginStorage { local } | S::EndStorage { local } => !removed.contains(local),
            _ => true,
        });
    }
    locals.retain(|local| !removed.contains(&local.name));
}

/// The local a call terminator assigns its result to, unless the call is
/// already a call step.
fn call_destination(terminator: &T) -> Option<&MirLocalId> {
    match terminator {
        T::Call {
            destination: Some(destination),
            result: None,
            ..
        } => Some(destination),
        _ => None,
    }
}

/// Keep a scalar, enum, or boxed pointer as a call step when its sole reader is
/// in a single-entry continuation. The call stays where it ran. An unread
/// scalar temporary can discard the result entirely.
pub(super) fn call_steps(
    locals: &mut Vec<Place>,
    blocks: &mut [MirBlock],
    temporaries: &BTreeSet<MirLocalId>,
) {
    let mut reads = BTreeMap::<MirLocalId, (usize, usize)>::new();
    let mut named = BTreeSet::<MirLocalId>::new();
    let mut pointer_destinations = BTreeSet::new();
    let mut assigned = BTreeMap::<MirLocalId, usize>::new();
    let mut predecessors = vec![0usize; blocks.len()];
    for (index, block) in blocks.iter().enumerate() {
        let mut block_reads = BTreeMap::new();
        for statement in &block.statements {
            statement_uses(statement, &mut block_reads, &mut named);
            if let S::Assign {
                target: E::Local { name },
                ..
            } = statement
            {
                *assigned.entry(name.clone()).or_default() += 1;
            }
        }
        terminator_uses(&block.terminator, &mut block_reads, &mut named);
        for (name, count) in block_reads {
            reads.entry(name).or_insert((0, index)).0 += count;
        }
        if let Some(destination) = call_destination(&block.terminator) {
            *assigned.entry(destination.clone()).or_default() += 1;
            // Preserve destinations of unread pointer calls, including a
            // slot also written by a direct call on another path.
            if matches!(
                block.terminator,
                T::Call {
                    function: MirCallee::Pointer { .. },
                    ..
                }
            ) {
                pointer_destinations.insert(destination.clone());
            }
        }
        for target in successors(&block.terminator) {
            if let Some(count) = predecessors.get_mut(target) {
                *count += 1;
            }
        }
    }
    // Each local's mentions apart from storage markers and the call that
    // defines it: a tested-then-read result has exactly its test and its read.
    let mut mentions = BTreeMap::<MirLocalId, usize>::new();
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
    let types: BTreeMap<_, _> = locals
        .iter()
        .map(|local| (&local.name, &local.value_type))
        .collect();
    let mut removed = BTreeSet::new();
    let mut next_step = 0u32;
    for index in 0..blocks.len() {
        let T::Call {
            function,
            destination: Some(destination),
            target,
            result: None,
            ..
        } = &blocks[index].terminator
        else {
            continue;
        };
        let (function, destination, target, through_pointer) = (
            function.clone(),
            destination.clone(),
            *target,
            matches!(function, MirCallee::Pointer { .. }),
        );
        // A result its successor tests for a variant, then reads once in the
        // arm that variant takes, as a `for` loop's `match` on `next()` does:
        // the test keeps the result and the payload read ends it.
        if !through_pointer
            && temporaries.contains(&destination)
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
            match &mut blocks[target].terminator {
                T::If {
                    condition: E::VariantIs { value, .. },
                    ..
                } => **value = result(true),
                T::Switch { scrutinee, .. } => *scrutinee = result(true),
                _ => unreachable!("selected a variant test"),
            }
            if let S::Assign {
                value: E::EnumField { base, .. },
                ..
            } = &mut blocks[arm].statements[position]
            {
                **base = result(false);
            }
            if let T::Call {
                destination,
                result,
                ..
            } = &mut blocks[index].terminator
            {
                *destination = None;
                *result = Some(call);
            }
            next_step += 1;
            removed.insert(destination);
            continue;
        }
        let Some(ty) = types.get(&destination) else {
            continue;
        };
        if !through_pointer
            && matches!(ty, Type::Enum { .. })
            && temporaries.contains(&destination)
            && assigned.get(&destination) == Some(&1)
            && target > index
            && predecessors.get(target) == Some(&1)
            && fold_nested_enum_call_match(
                blocks,
                target,
                &destination,
                &function,
                next_step,
                &predecessors,
                mentions.get(&destination).copied().unwrap_or_default(),
            )
        {
            if let T::Call {
                destination: slot,
                result,
                ..
            } = &mut blocks[index].terminator
            {
                *slot = None;
                *result = Some(next_step);
            }
            next_step += 1;
            removed.insert(destination);
            continue;
        }
        // A by-value argument can consume the preceding call's owned result
        // directly. The producer has already materialized it, and the next
        // call will initialize its own parameter from it.
        if let Type::Record { name } = ty
            && !through_pointer
            && temporaries.contains(&destination)
            && assigned.get(&destination) == Some(&1)
            && reads.get(&destination) == Some(&(1, target))
            && mentions.get(&destination) == Some(&1)
            && target != index
            && predecessors.get(target) == Some(&1)
            && let Ok([producer, consumer]) = blocks.get_disjoint_mut([index, target])
            && consumer
                .statements
                .iter()
                .all(|statement| matches!(statement, S::Site { .. } | S::EndStorage { .. }))
            && let T::Call {
                arguments,
                owned_arguments,
                function: MirCallee::Direct(_),
                ..
            } = &mut consumer.terminator
            && let Some(argument) = owned_arguments.iter_mut().find(|argument| {
                argument.moved
                    && argument.record == *name
                    && argument.local.as_ref() == Some(&destination)
            })
            && let Some(operand @ E::Local { .. }) = arguments.get_mut(argument.index)
            && matches!(operand, E::Local { name } if *name == destination)
        {
            *operand = E::CallResult {
                call: next_step,
                function,
                keeps: false,
            };
            argument.local = None;
            let T::Call {
                destination: slot,
                result,
                ..
            } = &mut producer.terminator
            else {
                unreachable!("selected a direct call");
            };
            *slot = None;
            *result = Some(next_step);
            next_step += 1;
            removed.insert(destination);
            continue;
        }
        if !temporaries.contains(&destination) || named.contains(&destination) {
            continue;
        }
        // Alternative calls can write the same unused result slot. With no
        // other write or use, each call can discard its result independently.
        if ty.is_scalar()
            && !pointer_destinations.contains(&destination)
            && !reads.contains_key(&destination)
            && !mentions.contains_key(&destination)
        {
            if let T::Call { destination, .. } = &mut blocks[index].terminator {
                *destination = None;
            }
            removed.insert(destination);
            continue;
        }
        if assigned.get(&destination) != Some(&1) {
            continue;
        }
        let Some(&(1, reader)) = reads.get(&destination) else {
            continue;
        };
        let boxed = matches!(ty, Type::Box { .. } | Type::OptionBox { .. });
        if !(ty.is_scalar() || matches!(ty, Type::Enum { .. }) || boxed)
            || (through_pointer && (!ty.is_scalar() || reader != target))
            || target == index
            || predecessors.get(target) != Some(&1)
        {
            continue;
        }
        // In `[f(), g()]` the first result is read after the second call.
        // Each edge in this continuation must be forward and single-entry.
        // Box and optional-box results are retained only to the immediate continuation.
        if reader != target
            && (boxed
                || !(index < target
                    && target < reader
                    && predecessors.get(reader) == Some(&1)
                    && matches!(blocks[target].terminator,
                    T::Call { target, function: MirCallee::Direct(_), .. } if target == reader)))
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
        let successor = &mut blocks[reader];
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
        // A use that cannot take an expression still needs its local.
        if !values.is_empty() {
            continue;
        }
        if let T::Call {
            destination,
            result,
            ..
        } = &mut blocks[index].terminator
        {
            *destination = None;
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

/// A `?` carrier relays a call result to the variant test and to one use
/// in each arm. Keep the call result through the test, then end it on the
/// path that reads either the success payload or the residual.
pub(super) fn fold_try_result_aliases(
    locals: &mut Vec<Place>,
    blocks: &mut [MirBlock],
    temporaries: &BTreeSet<MirLocalId>,
) {
    use super::super::schema::SwitchLabel;
    let transparent = |statement: &S| {
        matches!(
            statement,
            S::Site { .. } | S::BeginStorage { .. } | S::EndStorage { .. }
        )
    };
    if !blocks
        .iter()
        .flat_map(|block| &block.statements)
        .any(|statement| {
            matches!(statement, S::Assign {
            target: E::Local { name },
            value: E::CallResult { .. },
        } if temporaries.contains(name))
        })
    {
        return;
    }
    let mut mentions = BTreeMap::<MirLocalId, usize>::new();
    let mut predecessors = vec![0usize; blocks.len()];
    for block in blocks.iter() {
        for statement in block.statements.iter().filter(|s| !transparent(s)) {
            for name in mentioned_locals(statement) {
                *mentions.entry(name).or_default() += 1;
            }
        }
        let mut reads = BTreeMap::new();
        let mut named = BTreeSet::new();
        terminator_uses(&block.terminator, &mut reads, &mut named);
        named.extend(reads.into_keys());
        named.extend(call_destination(&block.terminator).cloned());
        for name in named {
            *mentions.entry(name).or_default() += 1;
        }
        for successor in successors(&block.terminator) {
            if let Some(count) = predecessors.get_mut(successor) {
                *count += 1;
            }
        }
    }
    let mut removed = BTreeSet::new();
    for index in 0..blocks.len() {
        let block = &blocks[index];
        let T::Goto { target } = block.terminator else {
            continue;
        };
        if target <= index || predecessors.get(target) != Some(&1) {
            continue;
        }
        let mut statements = block
            .statements
            .iter()
            .enumerate()
            .filter(|(_, s)| !transparent(s));
        let Some((
            definition,
            S::Assign {
                target: E::Local { name },
                value:
                    E::CallResult {
                        call,
                        function,
                        keeps: false,
                    },
            },
        )) = statements.next()
        else {
            continue;
        };
        if statements.next().is_some()
            || !temporaries.contains(name)
            || mentions.get(name) != Some(&4)
        {
            continue;
        }
        let test = &blocks[target];
        let T::Switch {
            scrutinee: E::Local { name: tested },
            cases,
            otherwise: None,
        } = &test.terminator
        else {
            continue;
        };
        let [first, second] = cases.as_slice() else {
            continue;
        };
        if tested != name
            || first.target == second.target
            || !test.statements.iter().all(transparent)
        {
            continue;
        }
        let use_in = |case: &super::super::schema::SwitchCase| {
            let SwitchLabel::Variant { name: variant } = &case.label else {
                return None;
            };
            let arm = case.target;
            if arm <= target || predecessors.get(arm) != Some(&1) {
                return None;
            }
            let (position, statement) = blocks[arm]
                .statements
                .iter()
                .enumerate()
                .find(|(_, statement)| !transparent(statement))?;
            let S::Assign {
                target: E::Local { .. },
                value,
            } = statement
            else {
                return None;
            };
            match value {
                E::EnumField {
                    base,
                    variant: read,
                    ..
                } if read == variant
                    && matches!(base.as_ref(), E::Local { name: source } if source == name) =>
                {
                    Some((position, false))
                }
                E::Local { name: source } if source == name => Some((position, true)),
                _ => None,
            }
        };
        let (Some((first_use, first_whole)), Some((second_use, second_whole))) =
            (use_in(first), use_in(second))
        else {
            continue;
        };
        if first_whole == second_whole {
            continue;
        }
        let arms = [(first.target, first_use), (second.target, second_use)];
        let (name, function, call) = (name.clone(), function.clone(), *call);
        let result = |keeps| E::CallResult {
            call,
            function: function.clone(),
            keeps,
        };
        if let T::Switch { scrutinee, .. } = &mut blocks[target].terminator {
            *scrutinee = result(true);
        }
        for (arm, position) in arms {
            if let S::Assign { value, .. } = &mut blocks[arm].statements[position] {
                match value {
                    E::EnumField { base, .. } => **base = result(false),
                    _ => *value = result(false),
                }
            }
        }
        blocks[index].statements.remove(definition);
        removed.insert(name);
    }
    if removed.is_empty() {
        return;
    }
    for block in blocks {
        block.statements.retain(|statement| match statement {
            S::BeginStorage { local } | S::EndStorage { local } => !removed.contains(local),
            _ => true,
        });
    }
    locals.retain(|local| !removed.contains(&local.name));
}

/// Retain a call result through two nested binary enum matches whose leaves
/// return. The caller's result is the source of each projection, even if
/// one of the paths returns without reading a payload.
fn fold_nested_enum_call_match(
    blocks: &mut [MirBlock],
    outer: usize,
    destination: &MirLocalId,
    function: &MirCallee,
    call: u32,
    predecessors: &[usize],
    mentions: usize,
) -> bool {
    use super::super::schema::SwitchLabel;

    fn projection_base(mut value: &E) -> Option<&MirLocalId> {
        while let E::EnumField { base, .. } = value {
            if let E::Local { name } = base.as_ref() {
                return Some(name);
            }
            value = base;
        }
        None
    }

    let targets = |block: &MirBlock| -> Option<[usize; 2]> {
        let T::Switch {
            cases, otherwise, ..
        } = &block.terminator
        else {
            return None;
        };
        let pair = match (cases.as_slice(), otherwise) {
            ([first, second], None) if matches!(second.label, SwitchLabel::Variant { .. }) => {
                (first, second.target)
            }
            ([first], Some(otherwise)) => (first, *otherwise),
            _ => return None,
        };
        (matches!(pair.0.label, SwitchLabel::Variant { .. }) && pair.0.target != pair.1)
            .then_some([pair.0.target, pair.1])
    };
    let transparent = |statement: &S| {
        matches!(
            statement,
            S::Site { .. } | S::BeginStorage { .. } | S::EndStorage { .. }
        )
    };
    if !matches!(&blocks[outer].terminator, T::Switch { scrutinee: E::Local { name }, .. } if name == destination)
        || !blocks[outer].statements.iter().all(transparent)
    {
        return false;
    }
    let Some(outer_targets) = targets(&blocks[outer]) else {
        return false;
    };
    let Some(inner) = outer_targets.into_iter().find(|&target| {
        matches!(&blocks[target].terminator, T::Switch { scrutinee, .. }
            if projection_base(scrutinee) == Some(destination))
    }) else {
        return false;
    };
    if inner <= outer
        || predecessors[inner] != 1
        || !blocks[inner].statements.iter().all(transparent)
    {
        return false;
    }
    let Some(inner_targets) = targets(&blocks[inner]) else {
        return false;
    };
    let mut entries = BTreeMap::<usize, usize>::new();
    for target in outer_targets
        .into_iter()
        .filter(|target| *target != inner)
        .chain(inner_targets)
    {
        *entries.entry(target).or_default() += 1;
    }
    let mut reads = Vec::new();
    for (leaf, entries) in entries {
        if leaf <= outer
            || leaf == inner
            || predecessors[leaf] != entries
            || !matches!(blocks[leaf].terminator, T::Return)
        {
            return false;
        }
        let mut payload = None;
        for (position, statement) in blocks[leaf].statements.iter().enumerate() {
            if let S::Assign {
                target: E::Local { .. },
                value,
            } = statement
                && projection_base(value) == Some(destination)
                && payload.replace(position).is_some()
            {
                return false;
            }
        }
        reads.extend(payload.map(|position| (leaf, position)));
    }
    if mentions != 2 + reads.len() {
        return false;
    }

    let substitute = |value: &mut E, keeps| {
        put_back(
            value,
            &BTreeMap::from([(
                destination.clone(),
                E::CallResult {
                    call,
                    function: function.clone(),
                    keeps,
                },
            )]),
        );
    };
    for index in [outer, inner] {
        if let T::Switch { scrutinee, .. } = &mut blocks[index].terminator {
            substitute(scrutinee, true);
        }
    }
    for (leaf, position) in reads {
        if let S::Assign { value, .. } = &mut blocks[leaf].statements[position] {
            substitute(value, false);
        }
    }
    true
}

/// The arm a test of `destination`'s variant takes when it holds, and the
/// position there of the arm's one read of it, its payload: `(arm, i)` when
/// `dispatch` only tests `destination` and the arm, entered only from that
/// test, reads its field first.
fn tested_then_read(
    blocks: &[MirBlock],
    destination: &MirLocalId,
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
    if !block.statements.iter().all(transparent) {
        return None;
    }
    let payload_read = |arm: usize, variant: &str| {
        if predecessors.get(arm) != Some(&1) {
            return None;
        }
        let arm_block = blocks.get(arm)?;
        let position = arm_block
            .statements
            .iter()
            .position(|statement| !transparent(statement))?;
        let S::Assign {
            value:
                E::EnumField {
                    base,
                    variant: read,
                    ..
                },
            ..
        } = &arm_block.statements[position]
        else {
            return None;
        };
        (matches!(base.as_ref(), E::Local { name } if name == destination) && read == variant)
            .then_some((arm, position))
    };
    match &block.terminator {
        T::If {
            condition: E::VariantIs { value, variant },
            then_target,
            ..
        } if matches!(value.as_ref(), E::Local { name } if name == destination) => {
            payload_read(*then_target, variant)
        }
        T::Switch {
            scrutinee: E::Local { name },
            cases,
            otherwise: None,
        } if name == destination && cases.len() == 2 && cases[0].target != cases[1].target => {
            cases.iter().find_map(|case| {
                let super::super::schema::SwitchLabel::Variant { name } = &case.label else {
                    return None;
                };
                payload_read(case.target, name)
            })
        }
        _ => None,
    }
}

fn successors(terminator: &T) -> Vec<usize> {
    match terminator {
        T::Goto { target }
        | T::Drop { target, .. }
        | T::Call { target, .. }
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
/// Whether `value` is an array literal or repeat whose elements are pure.
fn pure_array(value: &E) -> bool {
    match value {
        E::Array { elements } => elements.iter().all(pure),
        E::Repeat { value, .. } => pure(value),
        _ => false,
    }
}

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
        // A call has effects; a borrow begins a borrow; a slice and the
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
fn statement_named_locals(statement: &S) -> Vec<&MirLocalId> {
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
        S::EnumerateNext {
            iterator,
            option,
            index,
            element,
            ..
        } => std::iter::once(iterator)
            .chain(option)
            .chain(index)
            .chain(element)
            .collect(),
        S::ChunkNext {
            iterator,
            option,
            payload,
            ..
        } => std::iter::once(iterator)
            .chain(option)
            .chain(payload)
            .collect(),
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
        | T::BoxFree { .. } => Vec::new(),
    }
}

fn terminator_named_locals(terminator: &T) -> Vec<&MirLocalId> {
    match terminator {
        T::Drop { local, .. } | T::BoxFree { local, .. } => vec![local],
        // A call's destination is counted apart, by `call_destination`.
        T::Call {
            function,
            owned_arguments,
            ..
        } => {
            let mut named = match function {
                MirCallee::Direct(_) => Vec::new(),
                MirCallee::Pointer { local } => vec![local],
            };
            named.extend(
                owned_arguments
                    .iter()
                    .filter_map(|argument| argument.local.as_ref()),
            );
            named
        }
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
    reads: &mut BTreeMap<MirLocalId, usize>,
    named: &mut BTreeSet<MirLocalId>,
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
fn target_uses(
    target: &E,
    reads: &mut BTreeMap<MirLocalId, usize>,
    named: &mut BTreeSet<MirLocalId>,
) {
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

fn enum_switch_local(terminator: &T) -> Option<&MirLocalId> {
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
        Some(name)
    } else {
        None
    }
}

fn terminator_uses(
    terminator: &T,
    reads: &mut BTreeMap<MirLocalId, usize>,
    named: &mut BTreeSet<MirLocalId>,
) {
    // A match splits a proof by its scrutinee's variants. This use must
    // continue to name a binding.
    if let Some(name) = enum_switch_local(terminator) {
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
    reads: &mut BTreeMap<MirLocalId, usize>,
    named: &mut BTreeSet<MirLocalId>,
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
        E::Call { arguments, .. } => {
            for argument in arguments {
                expression_uses(argument, reads, named);
            }
        }
        E::Borrow { place, .. } => place_uses(place, reads, named),
        E::Field { base, .. } => place_uses(base, reads, named),
        // An enum payload projected from a value reads the enum's value.
        E::EnumField { base, .. } => expression_uses(base, reads, named),
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
fn place_root(place: &E) -> Option<&MirLocalId> {
    match place {
        E::Local { name } => Some(name),
        E::Field { base, .. } => place_root(base),
        _ => None,
    }
}

/// Every local `statement` names: those it reads, assigns, or names by a
/// field.
fn mentioned_locals(statement: &S) -> BTreeSet<MirLocalId> {
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
fn place_uses(
    place: &E,
    reads: &mut BTreeMap<MirLocalId, usize>,
    named: &mut BTreeSet<MirLocalId>,
) {
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
    values: &'a mut BTreeMap<MirLocalId, E>,
    refused: Vec<(MirLocalId, E)>,
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
        && let Some(value) = pending.values.remove(name)
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
fn substitute_statement(
    statement: &mut S,
    values: &mut BTreeMap<MirLocalId, E>,
) -> Vec<(MirLocalId, E)> {
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
fn substitute_terminator(
    terminator: &mut T,
    values: &mut BTreeMap<MirLocalId, E>,
) -> Vec<(MirLocalId, E)> {
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
        Expression as E, MirBlock, MirCallee, MirLocalId, MirStatement as S, MirTerminator as T,
        Place, Span, SwitchCase, SwitchLabel, Type,
    };
    use std::collections::{BTreeMap, BTreeSet};

    fn callee(name: &str, pointer: bool) -> MirCallee {
        if pointer {
            MirCallee::Pointer { local: name.into() }
        } else {
            MirCallee::Direct(name.into())
        }
    }

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

    #[test]
    fn callback_copy_only_folds_when_the_source_cannot_change() {
        let pointer = Type::FnPointer {
            parameters: vec![],
            result: Box::new(Type::Unit),
        };
        let parameters = BTreeMap::from([("f".into(), pointer.clone())]);
        let borrowed = E::Borrow {
            place: Box::new(local("f")),
            value_type: Type::Reference {
                mutable: true,
                pointee: Box::new(pointer.clone()),
            },
        };
        for change in [
            None,
            Some(assign("f", local("other"))),
            Some(assign("r", borrowed)),
        ] {
            let folded = change.is_none();
            let mut locals = vec![Place {
                value_type: pointer.clone(),
                ..place("t1")
            }];
            let mut statements = vec![assign("t1", local("f"))];
            statements.extend(change);
            let call = |function: &str, through_pointer, target| T::Call {
                function: callee(function, through_pointer),
                target,
                arguments: vec![],
                owned_arguments: vec![],
                destination: None,
                result: None,
            };
            let mut blocks = [
                block(statements, call("evaluate_argument", false, 1)),
                block(vec![], call("t1", true, 2)),
                block(vec![], T::Return),
            ];
            super::fold_callback_copies(
                &mut locals,
                &mut blocks,
                &BTreeSet::from(["t1".into()]),
                &parameters,
            );
            assert_eq!(locals.is_empty(), folded);
            let expected = if folded { "f" } else { "t1" };
            assert!(
                matches!(&blocks[1].terminator, T::Call { function, .. } if function.source_name() == Some(expected))
            );
        }
    }

    /// Runs the pass over one block with temporaries `t1` and `t2`.
    fn substituted(statements: Vec<S>, terminator: T) -> (Vec<MirLocalId>, MirBlock) {
        let mut locals = ["a", "b", "x", "t1", "t2"].map(place).to_vec();
        let mut blocks = vec![MirBlock {
            terminator_site: None,
            statements,
            terminator,
        }];
        let temporaries = BTreeSet::from(["t1".into(), "t2".into()]);
        super::substitute_pure_values(&mut locals, &mut blocks, &temporaries, &BTreeSet::new());
        let names = locals.into_iter().map(|local| local.name).collect();
        (names, blocks.pop().unwrap())
    }

    #[test]
    fn a_closure_moves_only_into_its_immediate_first_argument() {
        let closure = E::ClosureInstance {
            function: "closure_body".into(),
            captures: vec![local("a")],
            value_type: Type::FnPointer {
                parameters: vec![Type::U32],
                result: Box::new(Type::U32),
            },
        };
        for (arguments, intervening_write, folded) in [
            (vec![local("t1"), local("b")], false, true),
            (vec![local("b"), local("t1")], false, false),
            (vec![local("t1"), local("t1")], false, false),
            (vec![local("t1"), local("b")], true, false),
        ] {
            let mut statements = vec![assign("t1", closure.clone())];
            statements.extend(intervening_write.then(|| assign("a", local("b"))));
            let (locals, block) = substituted(
                statements,
                T::Call {
                    function: "apply".into(),
                    arguments,
                    owned_arguments: vec![],
                    destination: None,
                    target: 1,
                    result: None,
                },
            );
            assert_eq!(!locals.iter().any(|name| name == "t1"), folded);
            let T::Call { arguments, .. } = block.terminator else {
                unreachable!("the call remains in place");
            };
            assert_eq!(matches!(arguments[0], E::ClosureInstance { .. }), folded);
        }
    }

    #[test]
    fn constructor_reborrow_crosses_a_copy_but_not_a_rebinding() {
        let borrow = E::Borrow {
            place: Box::new(E::Deref {
                reference: Box::new(local("a")),
                value_type: Type::U32,
            }),
            value_type: Type::Reference {
                mutable: true,
                pointee: Box::new(Type::U32),
            },
        };
        for rebind in [false, true] {
            let copied = if rebind { "a" } else { "t2" };
            let mut locals = vec![place("t1")];
            let mut blocks = [block(
                vec![
                    assign("t1", borrow.clone()),
                    assign(copied, local("b")),
                    S::Initialize {
                        target: "guard".into(),
                        record: "Guard".into(),
                        fields: vec![local("t1"), local(copied)],
                    },
                ],
                T::Return,
            )];
            super::fold_constructor_reborrows(
                &mut locals,
                &mut blocks,
                &BTreeSet::from(["t1".into()]),
            );
            assert_eq!(locals.is_empty(), !rebind);
            assert!(matches!(&blocks[0].statements.last(),
                Some(S::Initialize { fields, .. })
                    if matches!(fields[0], E::Borrow { .. }) != rebind));
        }
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
    fn a_scalar_operand_crosses_only_its_own_straight_line_goto() {
        let length = E::SliceLength {
            slice: Box::new(E::Borrow {
                place: Box::new(local("source")),
                value_type: Type::ByteSlice { mutable: false },
            }),
        };
        let conversion = E::IntegerFrom {
            value: Box::new(local("source")),
            source_type: Type::U8,
            value_type: Type::U32,
        };
        let cast = E::Cast {
            value: Box::new(local("t1")),
            value_type: Type::U32,
        };
        for (intrinsic, source_type, temporary_type) in [
            (length, Type::ByteSlice { mutable: false }, Type::Usize),
            (conversion, Type::U8, Type::U32),
            (local("source"), Type::U32, Type::U32),
        ] {
            for (site, storage, second_entry, folded) in [
                (1, "t1", false, true),
                (2, "t1", false, false),
                (1, "source", false, false),
                (1, "t1", true, false),
            ] {
                let mut blocks = vec![
                    MirBlock {
                        terminator_site: Some(1),
                        statements: vec![S::Site { site: 1 }, assign("t1", intrinsic.clone())],
                        terminator: T::Goto { target: 1 },
                    },
                    MirBlock {
                        terminator_site: Some(site),
                        statements: vec![
                            S::Site { site },
                            S::EndStorage {
                                local: storage.into(),
                            },
                            assign("x", binary("add", local("a"), cast.clone())),
                        ],
                        terminator: T::Return,
                    },
                ];
                if second_entry {
                    blocks.push(MirBlock {
                        terminator_site: Some(1),
                        statements: Vec::new(),
                        terminator: T::Goto { target: 1 },
                    });
                }
                let mut source = place("source");
                source.value_type = source_type.clone();
                let mut temporary = place("t1");
                temporary.value_type = temporary_type.clone();
                let mut locals = vec![source, place("a"), place("x"), temporary];
                super::substitute_pure_values(
                    &mut locals,
                    &mut blocks,
                    &BTreeSet::from(["t1".into()]),
                    &BTreeSet::new(),
                );
                assert_eq!(!locals.iter().any(|local| local.name == "t1"), folded);
                assert!(matches!(
                    blocks[1].statements.last(),
                    Some(S::Assign { value: E::Binary { right, .. }, .. })
                        if matches!(right.as_ref(), E::Cast { value, .. }
                            if matches!(value.as_ref(), E::Local { name } if name == "t1") != folded)
                ));
            }
        }
    }

    #[test]
    fn the_slice_length_does_not_rebind_a_copied_loop_index() {
        let borrow = E::Borrow {
            place: Box::new(local("bytes")),
            value_type: Type::ByteSlice { mutable: false },
        };
        for length_target in ["x", "a"] {
            let mut locals = ["a", "x", "t1", "t2"].map(place).to_vec();
            let mut blocks = [
                MirBlock {
                    terminator_site: Some(1),
                    statements: vec![
                        S::Site { site: 1 },
                        assign("t1", local("a")),
                        assign(
                            length_target,
                            E::SliceLength {
                                slice: Box::new(borrow.clone()),
                            },
                        ),
                    ],
                    terminator: T::Goto { target: 1 },
                },
                MirBlock {
                    terminator_site: Some(1),
                    statements: vec![S::Site { site: 1 }],
                    terminator: T::If {
                        condition: E::Not {
                            value: Box::new(binary("lt", local("t1"), local("x"))),
                        },
                        then_target: 2,
                        else_target: 0,
                    },
                },
                block(vec![], T::Return),
            ];
            super::substitute_pure_values(
                &mut locals,
                &mut blocks,
                &BTreeSet::from(["t1".into()]),
                &BTreeSet::new(),
            );
            assert_eq!(
                locals.iter().any(|local| local.name == "t1"),
                length_target == "a"
            );
            assert!(
                matches!(&blocks[1].terminator, T::If { condition: E::Not { value }, .. }
                if matches!(value.as_ref(), E::Binary { left, .. }
                    if matches!(left.as_ref(), E::Local { name } if name == if length_target == "a" { "t1" } else { "a" })))
            );
        }
    }

    #[test]
    fn an_array_reborrow_folds_only_into_the_adjacent_coercion() {
        let array = Type::Array {
            element: Box::new(Type::U8),
            length: 4,
        };
        let borrow = E::Borrow {
            place: Box::new(E::Deref {
                reference: Box::new(local("a")),
                value_type: array.clone(),
            }),
            value_type: Type::Reference {
                mutable: true,
                pointee: Box::new(array.clone()),
            },
        };
        for (chained, separated) in [(false, false), (false, true), (true, false)] {
            let mut statements = Vec::new();
            let operand = if chained {
                statements.push(assign("t2", borrow.clone()));
                E::Borrow {
                    place: Box::new(E::Deref {
                        reference: Box::new(local("t2")),
                        value_type: array.clone(),
                    }),
                    value_type: Type::Reference {
                        mutable: true,
                        pointee: Box::new(array.clone()),
                    },
                }
            } else {
                borrow.clone()
            };
            statements.push(assign("t1", operand));
            if separated {
                statements.push(assign("a", local("b")));
            }
            statements.push(assign(
                "x",
                E::ArrayToSlice {
                    array: Box::new(local("t1")),
                    mutable: true,
                },
            ));
            let (locals, block) = substituted(statements, T::Return);
            assert_eq!(locals.iter().any(|name| name == "t1"), separated);
            if chained {
                assert!(!locals.iter().any(|name| name == "t2"));
            }
            assert!(matches!(block.statements.last(),
                Some(S::Assign { value: E::ArrayToSlice { array, mutable: true }, .. })
                    if matches!(array.as_ref(), E::Borrow { .. }) != separated));
        }
    }

    #[test]
    fn a_constant_remainder_moves_into_its_cast_across_removed_storage() {
        let constant = E::Call {
            function: "modulus".into(),
            arguments: vec![],
        };
        let remainder = binary("rem", local("a"), constant);
        let cast = E::Cast {
            value: Box::new(local("t1")),
            value_type: Type::U16,
        };
        for (marker, folded) in [
            (S::EndStorage { local: "t2".into() }, true),
            (S::EndStorage { local: "a".into() }, false),
            (S::Site { site: 1 }, false),
        ] {
            let mut statements = vec![
                assign("t1", remainder.clone()),
                marker,
                assign("x", cast.clone()),
            ];
            let mut removed = BTreeSet::from(["t2".into()]);
            super::fold_constant_remainder_casts(
                &mut statements,
                &|name| name == "t1",
                &BTreeSet::from(["modulus".into()]),
                &mut removed,
            );
            assert_eq!(removed.contains(&MirLocalId::from("t1")), folded);
            assert!(matches!(
                &statements[2],
                S::Assign { value: E::Cast { value, .. }, .. }
                    if matches!(value.as_ref(), E::Binary { operator, .. } if operator == "rem") == folded
            ));
        }
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
        assert!(locals.contains(&MirLocalId::from("t1")));
        assert!(matches!(
            block.statements.as_slice(),
            [S::Assign { target: E::Local { name }, .. }, _] if name == "t1"
        ));
    }

    #[test]
    fn a_call_result_read_once_in_its_successor_is_a_call_step() {
        // `t1 = f(a) -> bb1; bb1: x = t1 + 1` reads the call's result as a
        // step, and `t1` is gone.
        for through_pointer in [false, true] {
            let mut locals = ["a", "x", "t1"].map(place).to_vec();
            let mut blocks = vec![
                MirBlock {
                    terminator_site: None,
                    statements: Vec::new(),
                    terminator: T::Call {
                        function: callee("f", through_pointer),
                        arguments: vec![local("a")],
                        owned_arguments: Vec::new(),
                        destination: Some("t1".into()),
                        target: 1,
                        result: None,
                    },
                },
                MirBlock {
                    terminator_site: None,
                    statements: vec![assign("x", binary("add", local("t1"), local("a")))],
                    terminator: T::Return,
                },
            ];
            let temporaries = BTreeSet::from(["t1".into()]);
            super::call_steps(&mut locals, &mut blocks, &temporaries);
            assert!(locals.iter().all(|local| local.name != "t1"));
            assert!(matches!(
                blocks[0].terminator,
                T::Call {
                    result: Some(0),
                    ref function,
                    ..
                } if *function == callee("f", through_pointer)
            ));
            assert!(matches!(
                blocks[1].statements.as_slice(),
                [S::Assign { value: E::Binary { left, .. }, .. }]
                    if matches!(left.as_ref(), E::CallResult { call: 0, function, .. } if function.source_name() == Some("f"))
            ));
        }
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
        assert!(!locals.contains(&MirLocalId::from("t1")));
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
        assert!(locals.contains(&MirLocalId::from("t1")));
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
                destination: Some("unit".into()),
                target: 0,
                result: None,
            },
            terminator_site: None,
        }];
        let temporaries = BTreeSet::from(["t1".into()]);
        super::substitute_pure_values(&mut locals, &mut blocks, &temporaries, &BTreeSet::new());
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
            destination: Some("unit".into()),
            target: 0,
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
        assert!(locals.contains(&MirLocalId::from("t1")));
    }

    #[test]
    fn a_borrow_a_named_local_takes_whole_is_its_value() {
        // `t1 = &mut a; x = t1` is `x = &mut a`.
        let (locals, block) = substituted(
            vec![assign("t1", borrow(local("a"))), assign("x", local("t1"))],
            T::Return,
        );
        assert!(!locals.contains(&MirLocalId::from("t1")));
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
        let temporaries = BTreeSet::from(["t1".into(), "t2".into()]);
        super::collapse_iterator_moves(&mut locals, &mut blocks, &temporaries);
        assert_eq!(
            locals
                .iter()
                .map(|local| local.name.source_name().unwrap())
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
        assert!(locals.contains(&MirLocalId::from("t1")));
        assert!(locals.contains(&MirLocalId::from("t2")));
    }

    #[test]
    fn enum_match_can_use_an_unchanged_parameter() {
        let enum_type = Type::Enum {
            name: "Option".into(),
        };
        let parameters = BTreeMap::from([("x".into(), enum_type.clone())]);
        for changed in [false, true] {
            let mut locals = vec![Place {
                value_type: enum_type.clone(),
                ..place("t1")
            }];
            let mut statements = vec![assign("t1", local("x"))];
            statements.extend(changed.then(|| assign("x", local("y"))));
            let mut blocks = [
                block(
                    statements,
                    T::Switch {
                        scrutinee: local("t1"),
                        cases: vec![SwitchCase {
                            label: SwitchLabel::Variant {
                                name: "Some".into(),
                            },
                            target: 1,
                        }],
                        otherwise: Some(1),
                    },
                ),
                block(vec![], T::Return),
            ];
            super::bind_copied_enum_scrutinees(
                &mut locals,
                &mut blocks,
                &BTreeSet::from(["t1".into()]),
                &parameters,
            );
            assert_eq!(locals.is_empty(), !changed);
            let expected = if changed { "t1" } else { "x" };
            assert!(
                matches!(&blocks[0].terminator, T::Switch { scrutinee: E::Local { name }, .. }
                if name == expected)
            );
        }
    }

    #[test]
    fn an_enum_payload_read_can_use_the_original_value() {
        let field = E::EnumField {
            base: Box::new(local("t1")),
            name: "Result".into(),
            variant: "Err".into(),
            index: 0,
        };
        let (locals, block) = substituted(
            vec![assign("t1", local("a")), assign("x", field.clone())],
            T::Return,
        );
        assert!(!locals.iter().any(|name| name == "t1"));
        assert!(matches!(block.statements.as_slice(),
            [S::Assign { value: E::EnumField { base, .. }, .. }]
                if matches!(base.as_ref(), E::Local { name } if name == "a")));

        let borrow = E::Borrow {
            place: Box::new(field),
            value_type: Type::Reference {
                mutable: false,
                pointee: Box::new(Type::U32),
            },
        };
        let (locals, _) = substituted(
            vec![assign("t1", local("a")), assign("x", borrow)],
            T::Return,
        );
        assert!(locals.iter().any(|name| name == "t1"));
    }

    fn block(statements: Vec<S>, terminator: T) -> MirBlock {
        MirBlock {
            terminator_site: None,
            statements,
            terminator,
        }
    }

    #[test]
    fn a_returned_length_keeps_the_slice_snapshot_across_a_write() {
        let shared = Type::ByteSlice { mutable: false };
        for write in [false, true] {
            let mut locals = vec![Place {
                value_type: shared.clone(),
                ..place("t1")
            }];
            let mut blocks = [
                block(vec![assign("t1", local("a"))], T::Goto { target: 1 }),
                block(
                    write.then(|| assign("a", local("b"))).into_iter().collect(),
                    T::ReturnValue {
                        value: E::SliceLength {
                            slice: Box::new(local("t1")),
                        },
                    },
                ),
            ];
            super::fold_returned_slice_lengths(
                &mut locals,
                &mut blocks,
                &BTreeSet::from(["t1".into()]),
            );
            assert_eq!(locals.is_empty(), !write);
            let expected = if write { "t1" } else { "a" };
            assert!(matches!(&blocks[1].terminator,
                T::ReturnValue { value: E::SliceLength { slice } }
                    if matches!(slice.as_ref(), E::Local { name } if name == expected)));
        }
    }

    #[test]
    fn alternative_calls_can_discard_their_shared_result() {
        let call = |function: &str, through_pointer| T::Call {
            function: callee(function, through_pointer),
            arguments: vec![],
            owned_arguments: vec![],
            destination: Some("t1".into()),
            target: 3,
            result: None,
        };
        for (pointer_call, other_write) in [(false, false), (true, false), (false, true)] {
            let mut locals = vec![place("t1")];
            let mut blocks = [
                block(
                    vec![],
                    T::If {
                        condition: local("x"),
                        then_target: 1,
                        else_target: 2,
                    },
                ),
                block(vec![], call("f", false)),
                block(vec![], call("g", pointer_call)),
                block(
                    other_write
                        .then(|| assign("t1", local("x")))
                        .into_iter()
                        .collect(),
                    T::Return,
                ),
            ];
            super::call_steps(&mut locals, &mut blocks, &BTreeSet::from(["t1".into()]));
            let discarded = !pointer_call && !other_write;
            assert_eq!(locals.is_empty(), discarded);
            for (block, expected) in blocks[1..3].iter().zip(["f", "g"]) {
                assert!(
                    matches!(&block.terminator, T::Call { function, destination, result: None, .. }
                    if function.source_name() == Some(expected) && destination.is_none() == discarded)
                );
            }
        }
    }

    #[test]
    fn split_bindings_keep_storage_with_another_read_or_entry() {
        for (another_read, another_entry) in [(false, false), (true, false), (false, true)] {
            let mut locals = ["t1", "t2", "left", "right"]
                .map(|name| Place {
                    value_type: Type::ByteSlice { mutable: false },
                    ..place(name)
                })
                .to_vec();
            let mut blocks = vec![
                MirBlock {
                    terminator_site: Some(1),
                    ..block(
                        vec![
                            S::Site { site: 1 },
                            S::SliceSplit {
                                slice: local("bytes"),
                                midpoint: E::UsizeInteger { value: 1 },
                                left: "t1".into(),
                                right: "t2".into(),
                            },
                        ],
                        T::Goto { target: 1 },
                    )
                },
                block(
                    vec![
                        S::Site { site: 1 },
                        assign("left", local("t1")),
                        S::BeginStorage {
                            local: "right".into(),
                        },
                        assign("right", local("t2")),
                        S::EndStorage { local: "t2".into() },
                    ],
                    if another_read {
                        T::ReturnValue { value: local("t1") }
                    } else {
                        T::Return
                    },
                ),
            ];
            if another_entry {
                blocks.push(block(Vec::new(), T::Goto { target: 1 }));
            }

            super::bind_split_slice_results(
                &mut locals,
                &mut blocks,
                &BTreeSet::from(["t1".into(), "t2".into()]),
            );

            if another_read || another_entry {
                assert_eq!(locals.len(), 4);
                assert!(matches!(
                    blocks[0].statements.last(),
                    Some(S::SliceSplit { left, right, .. }) if left == "t1" && right == "t2"
                ));
            } else {
                assert_eq!(locals.len(), 2);
                assert!(matches!(
                    blocks[0].statements.as_slice(),
                    [S::Site { .. }, S::BeginStorage { local }, S::SliceSplit {
                        left, right, ..
                    }] if left == "left" && right == "right" && local == "right"
                ));
                assert!(matches!(blocks[1].statements.as_slice(), [S::Site { .. }]));
            }
        }
    }

    #[test]
    fn copied_slice_payload_binds_a_written_local_at_the_yield() {
        let iterator = Place {
            value_type: Type::SharedArrayIterator {
                element: Box::new(Type::U32),
            },
            ..place("iter")
        };
        let reference = Place {
            value_type: Type::Reference {
                mutable: false,
                pointee: Box::new(Type::U32),
            },
            ..place("t1")
        };
        let load = E::Deref {
            reference: Box::new(local("t1")),
            value_type: Type::U32,
        };
        let temporaries = BTreeSet::from(["t1".into()]);
        for (binding_site, used_again) in [(1, false), (2, false), (1, true)] {
            let mut locals = vec![iterator.clone(), reference.clone(), place("value")];
            let mut blocks = [
                MirBlock {
                    terminator_site: Some(1),
                    ..block(
                        vec![
                            S::Site { site: 1 },
                            S::SharedArrayNext {
                                iterator: "iter".into(),
                                option: None,
                                payload: Some("t1".into()),
                                taken: Some(true),
                            },
                        ],
                        T::Goto { target: 1 },
                    )
                },
                block(
                    vec![
                        S::Site { site: binding_site },
                        S::BeginStorage {
                            local: "value".into(),
                        },
                        assign("value", load.clone()),
                        S::EndStorage { local: "t1".into() },
                    ],
                    T::Return,
                ),
            ];
            if used_again {
                blocks[1]
                    .statements
                    .insert(3, assign("value", load.clone()));
            }

            super::bind_copied_slice_elements(&mut locals, &mut blocks, &temporaries);

            if binding_site == 1 && !used_again {
                assert!(!locals.iter().any(|place| place.name == "t1"));
                assert!(matches!(
                    blocks[0].statements.as_slice(),
                    [S::Site { .. }, S::BeginStorage { local }, S::SharedArrayNext {
                        payload: Some(payload), ..
                    }] if local == "value" && payload == "value"
                ));
                assert!(matches!(blocks[1].statements.as_slice(), [S::Site { .. }]));
            } else {
                assert!(locals.iter().any(|place| place.name == "t1"));
                assert!(matches!(
                    blocks[0].statements.last(),
                    Some(S::SharedArrayNext { payload: Some(payload), .. }) if payload == "t1"
                ));
            }
        }
    }

    /// Runs the return-place pass over `blocks`, with locals `_0` and `x`.
    fn returned(mut blocks: Vec<MirBlock>) -> (Vec<MirLocalId>, Vec<MirBlock>) {
        let mut locals = ["result", "x"].map(place).to_vec();
        super::return_values(&mut locals, &mut blocks, &"result".into());
        (locals.into_iter().map(|local| local.name).collect(), blocks)
    }

    #[test]
    fn a_value_written_just_before_return_is_returned() {
        // `_0 = x + 1; goto 1;  1: StorageDead(x); return` is `return x + 1`.
        let (locals, blocks) = returned(vec![
            block(
                vec![assign(
                    "result",
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
                    destination: Some("result".into()),
                    target: 1,
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
            block(vec![assign("result", zero.clone())], T::Goto { target: 3 }),
            block(vec![assign("result", zero)], T::Goto { target: 3 }),
            block(vec![], T::Return),
        ]);
        assert_eq!(locals, ["result", "x"]);
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
                    destination: Some("t2".into()),
                    target: 1,
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
        let names: Vec<_> = locals
            .iter()
            .map(|local| local.name.source_name().unwrap())
            .collect();
        assert_eq!(names, ["x", "t3"]);
        assert_eq!(blocks[0].statements.len(), 1);
    }

    /// Runs the unchanging-value pass with parameter `p` and temporaries
    /// `t1` and `t2`.
    fn substituted_everywhere(blocks: Vec<MirBlock>) -> (Vec<MirLocalId>, Vec<MirBlock>) {
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
    fn a_record_reborrow_uses_only_an_unchanged_matching_parameter() {
        let record = Type::Record {
            name: "Slot".into(),
        };
        let reference = |mutable| Type::Reference {
            mutable,
            pointee: Box::new(record.clone()),
        };
        let parameters = BTreeMap::from([("slot".into(), reference(true))]);
        for (mutable, rebind, folded) in [
            (true, false, true),
            (false, false, false),
            (true, true, false),
        ] {
            let value_type = reference(mutable);
            let reborrow = E::Borrow {
                place: Box::new(E::Deref {
                    reference: Box::new(local("slot")),
                    value_type: record.clone(),
                }),
                value_type: value_type.clone(),
            };
            let call = |function: &str, target| T::Call {
                function: function.into(),
                arguments: vec![local("t1")],
                owned_arguments: vec![],
                destination: None,
                target,
                result: None,
            };
            let mut locals = vec![Place {
                value_type,
                ..place("t1")
            }];
            let mut blocks = [
                block(vec![assign("t1", reborrow)], call("f", 1)),
                block(
                    rebind
                        .then(|| assign("slot", local("other")))
                        .into_iter()
                        .collect(),
                    call("g", 2),
                ),
                block(vec![], T::Return),
            ];
            super::substitute_literals(
                &mut locals,
                &mut blocks,
                &BTreeSet::from(["t1".into()]),
                &parameters,
            );
            assert_eq!(locals.is_empty(), folded);
            let expected = if folded { "slot" } else { "t1" };
            for block in &blocks[..2] {
                assert!(matches!(&block.terminator, T::Call { arguments, .. }
                    if matches!(arguments.as_slice(), [E::Local { name }] if name == expected)));
            }
        }
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
            destination: Some("unit".into()),
            target,
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
        let names: Vec<_> = locals
            .iter()
            .map(|local| local.name.source_name().unwrap())
            .collect();
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
        let names: Vec<_> = locals
            .iter()
            .map(|local| local.name.source_name().unwrap())
            .collect();
        assert_eq!(names, ["x"]);
        assert!(matches!(
            blocks[0].statements.as_slice(),
            [S::Assign { value: E::SliceLength { slice }, .. }]
                if matches!(slice.as_ref(), E::Borrow { place, .. }
                    if matches!(place.as_ref(), E::Local { name } if name == "bytes"))
        ));
    }

    #[test]
    fn an_array_built_for_a_record_field_is_the_field_value() {
        // `t1 = [x; 4]; r = R { a: 0, w: t1 }` is `r = R { a: 0, w: [x; 4] }`.
        let repeat = E::Repeat {
            value: Box::new(local("x")),
            length: 4,
        };
        let (names, block) = substituted(
            vec![
                assign("t1", repeat.clone()),
                S::Initialize {
                    target: "a".into(),
                    record: "R".into(),
                    fields: vec![
                        E::UnsignedInteger {
                            value: 0,
                            value_type: Type::U32,
                        },
                        local("t1"),
                    ],
                },
            ],
            T::Return,
        );
        assert_eq!(names, ["a", "b", "x", "t2"]);
        assert!(matches!(
            block.statements.as_slice(),
            [S::Initialize { fields, .. }]
                if matches!(&fields[1], E::Repeat { length: 4, value } if matches!(value.as_ref(), E::Local { name } if name == "x"))
        ));
        // An array read anywhere else stays a temporary.
        let (names, _) = substituted(
            vec![assign("t1", repeat), assign("a", local("t1"))],
            T::Return,
        );
        assert!(names.contains(&MirLocalId::from("t1")));
    }

    #[test]
    fn a_record_moved_into_its_local_is_built_there() {
        // `t2 = R { x }; t1 = t2; goto; it = t1` is `it = R { x }`, at the
        // last move, after `it`'s storage starts.
        let mut locals = ["x", "it", "t1", "t2"].map(place).to_vec();
        let moved = |target: &str, source: &str| S::Move {
            target: target.into(),
            source: source.into(),
            record: "R".into(),
        };
        let mut blocks = vec![
            block(
                vec![
                    S::Initialize {
                        target: "t2".into(),
                        record: "R".into(),
                        fields: vec![local("x")],
                    },
                    moved("t1", "t2"),
                ],
                T::Goto { target: 1 },
            ),
            block(
                vec![S::BeginStorage { local: "it".into() }, moved("it", "t1")],
                T::Return,
            ),
        ];
        super::collapse_iterator_moves(
            &mut locals,
            &mut blocks,
            &BTreeSet::from(["t1".into(), "t2".into()]),
        );
        let names: Vec<_> = locals
            .iter()
            .map(|local| local.name.source_name().unwrap())
            .collect();
        assert_eq!(names, ["x", "it"]);
        assert!(blocks[0].statements.is_empty());
        assert!(matches!(
            blocks[1].statements.as_slice(),
            [S::BeginStorage { .. }, S::Initialize { target, .. }] if target == "it"
        ));
    }

    #[test]
    fn a_shared_slice_of_a_local_array_is_read_in_place() {
        // `t1 = &words[..]; x = len(t1)` is `x = len(&words[..])`.
        let slice = Type::ScalarSlice {
            element: Box::new(Type::U32),
            mutable: false,
        };
        let mut locals = vec![
            place("x"),
            place("words"),
            Place {
                value_type: slice.clone(),
                ..place("t1")
            },
        ];
        let mut blocks = vec![block(
            vec![
                assign(
                    "t1",
                    E::ArrayToSlice {
                        array: Box::new(E::Borrow {
                            place: Box::new(local("words")),
                            value_type: Type::Reference {
                                mutable: false,
                                pointee: Box::new(Type::Array {
                                    element: Box::new(Type::U32),
                                    length: 4,
                                }),
                            },
                        }),
                        mutable: false,
                    },
                ),
                assign(
                    "x",
                    E::SliceLength {
                        slice: Box::new(local("t1")),
                    },
                ),
            ],
            T::Return,
        )];
        super::substitute_literals(
            &mut locals,
            &mut blocks,
            &BTreeSet::from(["t1".into()]),
            &BTreeMap::new(),
        );
        let names: Vec<_> = locals
            .iter()
            .map(|local| local.name.source_name().unwrap())
            .collect();
        assert_eq!(names, ["x", "words"]);
        assert!(matches!(
            blocks[0].statements.as_slice(),
            [S::Assign { value: E::SliceLength { slice }, .. }]
                if matches!(slice.as_ref(), E::ArrayToSlice { .. })
        ));
    }
}
