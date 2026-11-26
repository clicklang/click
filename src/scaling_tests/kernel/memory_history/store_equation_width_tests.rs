// Naming a store equation's read records the store's width for that one
// cell and names one read. Neither step visits the other cells the state
// holds or the other stores of the step.

fn store_equation_work(unrelated: usize, stores: usize) -> usize {
    use crate::kernel::{ExecutionFacts, ExecutionPureFact};
    let _session = crate::kernel::VerificationSession::enter();
    let cell = |index: u64| {
        Address::new(
            "array".into(),
            AddressOffset::scale_int32(OldMachineTerm::Variable(Variable(index)), 4),
        )
    };
    let mut memory = SymbolicMemory::new().with_block("array", 1 << 20);
    for index in 0..unrelated as u64 {
        memory = memory.store(
            cell(989_900_000 + index),
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(989_800_000 + index))),
        );
    }
    let mut operands = Vec::new();
    for index in 0..stores as u64 {
        let before = memory.clone();
        let pointer = cell(989_600_000 + index);
        let value = ProgramValue::Int32(OldMachineTerm::Variable(Variable(989_700_000 + index)));
        memory = memory.store(pointer.clone(), value.clone());
        operands.push((before, memory.clone(), pointer, value));
    }
    // Include equation construction at store admission, not just extraction
    // of retained equations. SymbolicMemory-state fixture setup stays outside it.
    let (equations, work) = crate::instrumentation::measure_deterministic_work(|| {
        let facts: ExecutionFacts = operands
            .into_iter()
            .map(|(before, after, pointer, value)| {
                ExecutionPureFact::certified_store(
                    before,
                    crate::kernel::ProgramPoint::of_memory(&after),
                    pointer,
                    value,
                    None,
                )
            })
            .collect::<Vec<_>>()
            .into();
        certified_store_equations(&facts)
    });
    assert_eq!(equations.len(), stores);
    work
}

#[test]
fn store_equation_naming_is_independent_of_unrelated_cells() {
    let baseline = store_equation_work(4, 1);
    for unrelated in [16, 64, 256] {
        assert_eq!(
            store_equation_work(unrelated, 1),
            baseline,
            "{unrelated} unrelated cells"
        );
    }
}

#[test]
fn store_equation_naming_is_linear_in_the_step_stores() {
    let one = store_equation_work(4, 1);
    for stores in [4, 16, 64] {
        let work = store_equation_work(4, stores);
        assert!(
            work <= stores * one,
            "{stores} stores took {work}, one took {one}"
        );
    }
}
