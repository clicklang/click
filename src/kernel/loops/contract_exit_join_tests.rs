use super::*;
use std::sync::Arc;

#[test]
fn exit_disjunct_restates_model_getters_without_replacing_history() {
    let ty = crate::kernel::AlgebraicType {
        rigid: false,
        name: "ExitModel".into(),
        arguments: vec![],
        variants: vec![crate::kernel::AlgebraicVariantType {
            name: "Done".into(),
            fields: vec![],
        }]
        .into(),
        schemas: Arc::new(crate::kernel::AlgebraicSchemas::new(BTreeMap::new())),
    };
    let model = |id| crate::kernel::AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: crate::kernel::AlgebraicTermNode::Variable(Variable(id)),
    };
    let held = model(986_100);
    let fresh = model(986_101);
    let fact = |model| {
        Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::ClickFunctionApplication {
                    name: "pending".into(),
                    arguments: vec![crate::kernel::PureFunctionArgument::Algebraic(model)],
                },
                Bitvector32Term::Constant(0),
            ),
            true,
        )
    };
    let historical = fact(held.clone());
    let expected = fact(fresh.clone());
    let mut restatement = LoopExitRestatement::default();
    restatement.pin_resource_value(
        &AlgebraicValue::Algebraic(fresh),
        &AlgebraicValue::Algebraic(held),
    );
    let joined = restatement.restate(
        vec![ExecutionPureFact::new(historical.clone())].into(),
        vec![],
        empty_checked_loan_evidence_sequence(),
    );
    assert!(joined.disjunct.contains(&expected));
    assert!(!joined.disjunct.contains(&historical));
    assert!(joined.restated.contains(&expected));
    assert!(joined.stated.contains_proposition(&historical));
}

fn marker_exits(count: usize, ambient: usize) -> Vec<CState> {
    let mut memory = CMemory::new()
        .with_block("shared", (ambient * 4) as u32)
        .with_block("havoc:10000000", 0);
    for index in 0..ambient {
        memory = memory.store(
            Pointer {
                block: PointerBlock::Concrete("shared".into()),
                offset: PointerOffsetTerm::Constant((index * 4) as i64),
            },
            int32(index as u32),
        );
    }
    (0..count)
        .map(|index| {
            CState::new().with_memory(
                memory
                    .clone()
                    .with_block(format!("call-havoc:{}", index + 20000000).as_str(), 0),
            )
        })
        .collect()
}

fn measured_join(exits: &[CState]) -> (CState, usize) {
    let mut successor = exits[0].clone();
    let mut variables =
        KernelVariableGenerator::fresh_for_execution(BTreeSet::from([Variable(30000000)]));
    let mut budget = ExecutionBudget::default();
    let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
        let bookkeeping =
            join_loop_exit_storage_bookkeeping(&mut successor, exits, &mut variables, &mut budget)?;
        let abstracted = LoopExitAbstraction {
            locals: &[],
            uninitialized: &[],
            cells: &BTreeSet::new(),
            bookkeeping,
        };
        for state in exits {
            if let Some(difference) = loop_exit_residual_difference(
                &successor,
                state,
                &abstracted,
                &[],
                &PureFactContext::new(),
            ) {
                return Err(difference);
            }
        }
        Ok(())
    });
    result.unwrap();
    (successor, work)
}

#[test]
fn exit_difference_names_call_bindings_and_storage_metadata() {
    let _session = crate::kernel::VerificationSession::enter();
    let left = CState::new();
    let mut right = left.clone();
    right.resource_bindings = Some(Arc::new(BTreeMap::from([(Variable(1), Variable(2))])));
    right.next_local_frame = 3;
    right.enclosing_frame_holds_locals = true;
    let report = loop_exit_state_difference(&left, &right, &PureFactContext::new()).unwrap();
    assert!(
        report.contains("call resource bindings (successor: 0 entries; exit: 1 entries)"),
        "{report}"
    );
    assert!(
        report.contains("next automatic-storage frame (successor: 0; exit: 3)"),
        "{report}"
    );
    assert!(
        report.contains("enclosing frame holds automatic objects (successor: false; exit: true)"),
        "{report}"
    );
    assert!(!report.contains("the symbolic state"), "{report}");
    assert!(loop_exit_state_difference(&left, &left, &PureFactContext::new()).is_none());
}

#[test]
fn exit_difference_does_not_blame_equivalent_creation_ledgers() {
    let _session = crate::kernel::VerificationSession::enter();
    let left = CState::new().with_population_creation_tracking();
    let mut right = CState::new().with_population_creation_tracking();
    right.next_local_frame = 3;
    let report = loop_exit_state_difference(&left, &right, &PureFactContext::new()).unwrap();
    assert!(report.contains("next automatic-storage frame"), "{report}");
    assert!(!report.contains("population effects"), "{report}");
}

#[test]
fn exit_difference_names_missing_locals_from_either_side_and_bounds_names() {
    let _session = crate::kernel::VerificationSession::enter();
    let left = CState::new();
    let mut right = left.clone();
    for index in 0..20 {
        right = right.with_local(format!("only_exit_{index:02}"), int32(0));
    }
    for (first, second) in [(&left, &right), (&right, &left)] {
        let report = loop_exit_state_difference(first, second, &PureFactContext::new()).unwrap();
        assert!(
            report.contains("only_exit_00") && report.contains("only_exit_11"),
            "{report}"
        );
        assert!(!report.contains("only_exit_12"), "{report}");
        assert!(report.contains("8 additional locals differ"), "{report}");
    }
}

#[test]
fn partial_value_binding_join_cannot_supply_a_missing_read_or_drop_declared_storage() {
    let _session = crate::kernel::VerificationSession::enter();
    let empty = CState::new();
    let value = empty.clone().with_local("temporary", int32(1));
    let body = c_assign("temporary", c_int32_literal(1));
    let mut exits = [empty.clone(), value.clone()];
    discard_loop_exit_partial_value_bindings(&empty, &body, &mut exits);
    assert!(
        exits
            .iter()
            .all(|state| state.locals.get("temporary").is_none())
    );
    assert!(loop_exit_state_difference(&exits[0], &exits[1], &PureFactContext::new()).is_none());

    let mut exits = [empty.clone(), value.clone()];
    discard_loop_exit_partial_value_bindings(&value, &body, &mut exits);
    assert!(
        exits[1].locals.get("temporary").is_some(),
        "entry bindings must remain checked"
    );

    let mut declared = value;
    if let Some(CLocalBinding::Object {
        storage_declared, ..
    }) = Arc::make_mut(&mut declared.locals.bindings).get_mut("temporary")
    {
        *storage_declared = true;
    }
    let mut exits = [empty.clone(), declared];
    discard_loop_exit_partial_value_bindings(&empty, &body, &mut exits);
    assert!(
        exits[1].locals.get("temporary").is_some(),
        "declared storage must remain checked"
    );
    assert!(loop_exit_state_difference(&exits[0], &exits[1], &PureFactContext::new()).is_some());
}

#[test]
fn numeric_float_equality_does_not_materialize_positive_zero_bits() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Pointer {
        block: PointerBlock::Concrete("shared".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block("shared", 4);
    let zero = CValue::Float32(Bitvector32Term::Constant(0));
    let load = symbolic_storage_cell_value(&memory, &pointer, CType::Float32, true).unwrap();
    // This equation also permits a negative-zero representation. Filling
    // the cache with positive-zero bits would make a later bitwise read false.
    let facts = [ExecutionPureFact::new(
        c_value_comparison_proposition(&load, CComparisonOperator::Equal, &zero).unwrap(),
    )];
    let mut states = vec![
        CState::new().with_memory(memory.clone().store(pointer.clone(), zero)),
        CState::new().with_memory(memory),
    ];
    retain_proven_loop_exit_cells(
        &mut states,
        &[&ExecutionFacts::new(), &facts.clone().into()],
        &PureFactContext::new(),
        true,
    )
    .unwrap();
    assert!(states[1].memory().known_value(&pointer).is_none());
}

#[test]
fn joined_call_epochs_do_not_transport_uncached_loads_or_hide_real_blocks() {
    let _session = crate::kernel::VerificationSession::enter();
    let exits = marker_exits(2, 4);
    let (successor, _) = measured_join(&exits);
    let pointer = Pointer {
        block: PointerBlock::Concrete("unknown".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let old_load =
        symbolic_storage_cell_value(exits[0].memory(), &pointer, CType::Int32, true).unwrap();
    let new_load =
        symbolic_storage_cell_value(successor.memory(), &pointer, CType::Int32, true).unwrap();
    let zero = int32(0);
    let old_fact =
        c_value_comparison_proposition(&old_load, CComparisonOperator::Equal, &zero).unwrap();
    let new_fact =
        c_value_comparison_proposition(&new_load, CComparisonOperator::Equal, &zero).unwrap();
    assert!(
        !PureFactContext::new()
            .assume_proposition(old_fact)
            .proves_atomic_without_search(&new_fact)
    );
    let changed = exits[1]
        .clone()
        .with_memory(exits[1].memory().clone().with_block("shared", 8));
    let abstracted = LoopExitAbstraction {
        locals: &[],
        uninitialized: &[],
        cells: &BTreeSet::new(),
        bookkeeping: true,
    };
    assert!(
        loop_exit_residual_difference(
            &successor,
            &changed,
            &abstracted,
            &[],
            &PureFactContext::new()
        )
        .unwrap()
        .contains("memory")
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/loops/contract_exit_join_tests.rs");
}
