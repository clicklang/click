use super::*;

#[test]
fn selecting_head_locals_does_not_scan_the_entry_environment() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut costs = Vec::new();
    for count in [16, 64, 256, 1024] {
        let mut entry = ExecutionState::new().with_local("selected", int32(0));
        for index in 0..count {
            entry = entry.with_local(format!("other{index}"), int32(index));
        }
        let mut variables = KernelVariableGenerator::fresh_for_execution(BTreeSet::new());
        let mut budget = ExecutionBudget::default();
        let (description, work) = crate::persistent::measure_persistent_work(|| {
            LoopHeadLocals::new(
                &entry,
                BTreeSet::from(["selected".into()]),
                &mut variables,
                &mut budget,
            )
            .unwrap()
        });
        assert_eq!(description.values.len(), 1);
        costs.push(work);
    }
    assert!(
        costs[0] > 0 && costs.iter().all(|cost| *cost <= 3 * costs[0]),
        "loop-head local selection: {costs:?}"
    );
}

#[test]
fn loop_head_havoc_ignores_private_scalar_slots() {
    use crate::kernel::primitives::{
        capture_block_registries, restore_block_registries, set_never_address_taken_locals,
    };

    let _session = crate::kernel::VerificationSession::enter();
    let registries = capture_block_registries();
    let names = (0..128)
        .map(|index| BindingName::from(format!("spare{index}")))
        .collect::<Vec<_>>();
    set_never_address_taken_locals(names.iter().cloned().collect());
    let written = Address::symbolic(Variable(954_020));
    let body = ProgramStatement::Store {
        pointer: ProgramExpression::Variable("p".into()),
        value: crate::kernel::program_expression::int32_literal(10),
    };
    let costs = [4, 16, 64, 128].map(|count| {
        let mut entry =
            ExecutionState::new().with_local("p", ProgramValue::pointer(written.clone()));
        let mut memory = SymbolicMemory::new().store(written.clone(), int32(9));
        for name in &names[..count] {
            entry = entry.with_local(name.clone(), int32(7));
            let slot = entry.locals.slot(name).unwrap();
            memory = memory.store(slot.clone(), int32(7));
        }
        let private = entry.locals.slot(&names[0]).unwrap().clone();
        let entry = entry.with_memory(memory);
        let mut variables = KernelVariableGenerator::fresh_for_execution(BTreeSet::new());
        let (after, work) = crate::instrumentation::measure_deterministic_work(|| {
            let escaped = address_escaped_scalar_locals(&entry, &body);
            havoc_loop_modified_locals(
                &entry,
                &body,
                &escaped,
                &mut variables,
                &mut ExecutionBudget::default(),
                None,
                None,
            )
            .unwrap()
        });
        assert_eq!(after.memory().known_value(&private), Some(int32(7)));
        assert_eq!(after.memory().known_value(&written), None);
        assert_eq!(entry.memory().known_value(&written), Some(int32(9)));
        work
    });
    restore_block_registries(&registries);
    let (min, max) = (costs.iter().min().unwrap(), costs.iter().max().unwrap());
    assert!(
        max - min <= 16,
        "loop-head havoc work with 4/16/64/128 private scalars: {costs:?}"
    );
}
