//! Common/native fold keys share the same scoped child walker and refusal rules.
use super::*;
use crate::kernel::{
    KernelFold, KernelFoldIndex, KernelTermExport, KernelType, MachineOperandView,
    SharedIntegerRangeEndpoint,
};

pub(super) fn bindings() -> AlphaBindings {
    AlphaBindings {
        integer: BTreeMap::new(),
        bitvector: BTreeMap::new(),
        algebraic: BTreeMap::new(),
        integer_scope: 0,
        bitvector_scope: 0,
        next_scope_id: 1,
        state_aware: true,
        checked_state_binder: None,
        raw_state_load_seen: false,
        registered_load_stack: BTreeSet::new(),
        registered_load_memo: HashMap::new(),
        pointer_load_stack: BTreeSet::new(),
        pointer_load_memo: HashMap::new(),
        load_interner: None,
        work_units: 0,
    }
}

pub(super) fn machine_fold_key<const ALLOW_LOADS: bool>(
    arguments: [MachineOperandView<'_>; 4],
    accumulator: Variable,
    item: Variable,
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaBitvectorKey> {
    let [start, end, initial, body] = arguments;
    let start = alpha_machine_key::<ALLOW_LOADS>(start, bindings, next_binder)?;
    let end = alpha_machine_key::<ALLOW_LOADS>(end, bindings, next_binder)?;
    let initial = alpha_machine_key::<ALLOW_LOADS>(initial, bindings, next_binder)?;
    let accumulator_ordinal = *next_binder;
    *next_binder = (*next_binder).checked_add(1)?;
    let item_ordinal = *next_binder;
    *next_binder = (*next_binder).checked_add(1)?;
    let bitvector_scope = bindings.next_scope_id;
    bindings.next_scope_id = bitvector_scope.checked_add(1)?;
    let previous_accumulator = bindings.bitvector.insert(accumulator, accumulator_ordinal);
    let previous_item = bindings.bitvector.insert(item, item_ordinal);
    let previous_scope = bindings.bitvector_scope;
    bindings.bitvector_scope = bitvector_scope;
    let body = alpha_machine_key::<ALLOW_LOADS>(body, bindings, next_binder);
    bindings.bitvector_scope = previous_scope;
    // Restore in reverse order even when the selected body refused a key.
    if let Some(previous) = previous_item {
        bindings.bitvector.insert(item, previous);
    } else {
        bindings.bitvector.remove(&item);
    }
    if let Some(previous) = previous_accumulator {
        bindings.bitvector.insert(accumulator, previous);
    } else {
        bindings.bitvector.remove(&accumulator);
    }
    Some(AlphaBitvectorKey::RangeFold {
        start: Box::new(start),
        end: Box::new(end),
        initial: Box::new(initial),
        body: Box::new(body?),
    })
}

pub(crate) fn integer_key(fold: &KernelFold) -> Option<IntegerFoldAlphaKey> {
    if fold.result_type() != &KernelType::Integer {
        return None;
    }
    let mut bindings = bindings();
    let mut next_binder = 0;
    let mut nodes = Vec::new();
    let mut memo = HashMap::new();
    let mut export = KernelTermExport::default();
    let [start, end, initial, body] = &fold.arguments;
    alpha_work_checkpoint(&mut bindings, 1)?;
    let index = match fold.index {
        KernelFoldIndex::Integer => {
            let start = export.integer(start).ok()?;
            let end = export.integer(end).ok()?;
            AlphaIntegerRangeIndex::Integer(
                alpha_integer_node(
                    &start,
                    &mut bindings,
                    &mut memo,
                    &mut nodes,
                    &mut next_binder,
                )?,
                alpha_integer_node(&end, &mut bindings, &mut memo, &mut nodes, &mut next_binder)?,
            )
        }
        KernelFoldIndex::Int32 | KernelFoldIndex::UInt64 => {
            // Use the same word interpretation and admission rule as the
            // existing Integer range endpoint wrapper.
            let start = SharedIntegerRangeEndpoint::from_shared(start.clone())?;
            let end = SharedIntegerRangeEndpoint::from_shared(end.clone())?;
            let start = alpha_machine_key::<false>(
                start.machine_operand().operand_view(),
                &mut bindings,
                &mut next_binder,
            )?;
            let end = alpha_machine_key::<false>(
                end.machine_operand().operand_view(),
                &mut bindings,
                &mut next_binder,
            )?;
            if fold.index == KernelFoldIndex::Int32 {
                AlphaIntegerRangeIndex::Int32(start, end)
            } else {
                AlphaIntegerRangeIndex::UInt64(start, end)
            }
        }
    };
    let initial = export.integer(initial).ok()?;
    let body = export.integer(body).ok()?;
    let initial = alpha_integer_node(
        &initial,
        &mut bindings,
        &mut memo,
        &mut nodes,
        &mut next_binder,
    )?;
    let node = alpha_integer_fold_node(
        index,
        initial,
        fold.accumulator,
        fold.item,
        &mut bindings,
        &mut next_binder,
        |bindings, next_binder| {
            alpha_integer_node(&body, bindings, &mut memo, &mut nodes, next_binder)
        },
    )?;
    let root = nodes.len();
    nodes.push(node);
    Some(IntegerFoldAlphaKey {
        key: AlphaIntegerKey { nodes, root },
        work_units: bindings.work_units,
    })
}

fn machine_key(fold: &KernelFold) -> Option<(AlphaBitvectorKey, usize)> {
    if fold.result_type() != &KernelType::Program(ProgramType::Int32) {
        return None;
    }
    let mut bindings = bindings();
    alpha_work_checkpoint(&mut bindings, 1)?;
    let key = machine_fold_key::<false>(
        fold.arguments.each_ref().map(MachineOperandView::Shared),
        fold.accumulator,
        fold.item,
        &mut bindings,
        &mut 0,
    )?;
    Some((key, bindings.work_units))
}

pub(crate) fn alpha_equivalent(left: &KernelFold, right: &KernelFold) -> Option<bool> {
    if left.result_type() != right.result_type() || left.index != right.index {
        return Some(false);
    }
    if left.result_type() == &KernelType::Integer {
        return integer_key(left)?.checked_eq(&integer_key(right)?);
    }
    let (left, left_work) = machine_key(left)?;
    let (right, right_work) = machine_key(right)?;
    if crate::instrumentation::deadline_exceeded_with_work(left_work.saturating_add(right_work)) {
        return None;
    }
    Some(left == right)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{IntegerRangeFoldIndex, KernelTerm, KernelTermImport};

    fn machine_fold(accumulator: u64, item: u64, body: MachineTerm) -> MachineTerm {
        MachineTerm::RangeFold {
            start: Box::new(MachineTerm::constant(0)),
            end: Box::new(MachineTerm::constant(9)),
            initial: Box::new(MachineTerm::Variable(Variable(80))),
            accumulator: Variable(accumulator),
            item: Variable(item),
            body: Box::new(body),
        }
    }

    #[test]
    fn common_machine_fold_keys_agree_with_native_binders_and_free_variables() {
        let left = machine_fold(81, 82, MachineTerm::Variable(Variable(81)));
        for right in [
            machine_fold(91, 92, MachineTerm::Variable(Variable(91))),
            machine_fold(91, 92, MachineTerm::Variable(Variable(81))),
            machine_fold(91, 92, MachineTerm::Variable(Variable(92))),
        ] {
            let expected = bitvector_folds_alpha_equivalent(&left, &right);
            assert!(expected.is_some());
            let left = KernelFold::import_machine(&mut KernelTermImport::default(), &left).unwrap();
            let right =
                KernelFold::import_machine(&mut KernelTermImport::default(), &right).unwrap();
            assert_eq!(alpha_equivalent(&left, &right), expected);
            assert_ne!(left, right);
        }
        let a = KernelFold::import_machine(&mut KernelTermImport::default(), &left).unwrap();
        assert_eq!(alpha_equivalent(&a, &a), Some(true));
    }

    #[test]
    fn common_integer_fold_keys_preserve_range_kind_and_outer_scope() {
        let native = |acc, item| IntegerTerm::RangeFold {
            index: IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::constant_i64(9).into(),
            },
            initial: IntegerTerm::Variable(Variable(81)).into(),
            accumulator: Variable(acc),
            item: Variable(item),
            body: IntegerTerm::Variable(Variable(acc)).into(),
        };
        let left = native(81, 82);
        let right = native(91, 92);
        let a = KernelFold::import_integer(&mut KernelTermImport::default(), &left).unwrap();
        let b = KernelFold::import_integer(&mut KernelTermImport::default(), &right).unwrap();
        assert_eq!(alpha_equivalent(&a, &b), Some(true));
        assert_eq!(
            integer_key(&a).unwrap(),
            integer_fold_alpha_key(&left.into()).unwrap()
        );
        let mut changed = b.clone();
        changed.arguments[2] = KernelTerm::variable(KernelType::Integer, Variable(91));
        assert_eq!(alpha_equivalent(&a, &changed), Some(false));
        let machine_bound = |format| {
            KernelTerm::retained_machine_operand(
                format,
                MachineOperandView::Legacy(&MachineTerm::Variable(Variable(80))),
            )
        };
        let fold = |kind, format| {
            KernelFold::new(
                kind,
                Variable(81),
                Variable(82),
                [
                    machine_bound(format),
                    machine_bound(format),
                    a.arguments[2].clone(),
                    a.arguments[3].clone(),
                ],
            )
            .unwrap()
        };
        let signed = fold(KernelFoldIndex::Int32, MachineIntegerType::Int32);
        let unsigned = fold(KernelFoldIndex::UInt64, MachineIntegerType::UInt64);
        assert_eq!(alpha_equivalent(&signed, &unsigned), Some(false));
        assert_eq!(alpha_equivalent(&signed, &signed), Some(true));
        for fold in [signed, unsigned] {
            let reference = fold
                .integer_compatibility(&mut KernelTermExport::default())
                .unwrap();
            assert_eq!(
                integer_key(&fold),
                integer_fold_alpha_key(&reference.into())
            );
        }
    }

    #[test]
    fn common_fold_keys_preserve_state_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = crate::kernel::SymbolicMemory::new();
        let pointer = Address::symbolic(Variable(101));
        let later = memory.clone().store(
            pointer.clone(),
            ProgramValue::Int32(MachineTerm::constant(1)),
        );
        let fold = |memory: &crate::kernel::SymbolicMemory| {
            let native = machine_fold(
                81,
                82,
                MachineTerm::MemoryLoad(
                    crate::kernel::ProgramPoint::at(&(crate::kernel::intern_memory_ref(memory))),
                    Box::new(pointer.clone()),
                    LoadKind::Int32,
                ),
            );
            KernelFold::import_machine(&mut KernelTermImport::default(), &native).unwrap()
        };
        let a = fold(&memory);
        let b = fold(&later);
        assert_eq!(alpha_equivalent(&a, &a), Some(true));
        assert_eq!(alpha_equivalent(&a, &b), Some(false));

        let to_integer = |machine: KernelFold| {
            let zero = KernelTerm::integer_literal(0.into());
            KernelFold::new(
                KernelFoldIndex::Int32,
                machine.accumulator,
                machine.item,
                [
                    machine.arguments[3].clone(),
                    machine.arguments[1].clone(),
                    zero.clone(),
                    zero,
                ],
            )
            .unwrap()
        };
        let a = to_integer(a);
        let b = to_integer(b);
        assert_eq!(alpha_equivalent(&a, &b), Some(false));
        let reference = a
            .integer_compatibility(&mut KernelTermExport::default())
            .unwrap();
        assert_eq!(integer_key(&a), integer_fold_alpha_key(&reference.into()));
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/fact_keys/fold_keys.rs");
}
