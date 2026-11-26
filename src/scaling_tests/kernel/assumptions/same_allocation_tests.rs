// Scaling tests of `same_allocation` decisions in `src/kernel/assumptions.rs`:
// deterministic work measured at several input sizes. Included into its
// `scaling_tests` module; see "Scaling tests" in `docs/internals/testing.md`.

use super::*;

fn parameter_pointer(variable: u64) -> OldPointer {
    OldPointer::new(
        OldAddress {
            base: AddressBase::ExternalArgument,
            offset: OldAddressOffset::scaled_int32_node(
                OldMachineTerm::Variable(Variable(variable)),
                4,
            ),
        },
        ProgramType::Int32Pointer,
    )
}

fn same_allocation(left: u64, right: u64) -> Proposition {
    crate::kernel::eval::same_allocation_proposition(
        &parameter_pointer(left),
        &parameter_pointer(right),
    )
}

fn measure(context: &PureFactContext, goal: &Proposition) -> (usize, usize) {
    let ((known, work), map_work) = crate::persistent::measure_persistent_work(|| {
        crate::instrumentation::measure_deterministic_work(|| context.contains_known(goal))
    });
    assert!(known, "the stated relation decides the goal");
    (work, map_work)
}

#[test]
fn same_allocation_decision_ignores_unrelated_facts() {
    let mut costs = Vec::new();
    for size in [8_u64, 32, 128, 512] {
        let mut context =
            PureFactContext::new().assume_proposition(same_allocation(81_000, 81_001));
        for index in 0..size {
            context =
                context.assume_proposition(same_allocation(82_000 + 2 * index, 82_001 + 2 * index));
        }
        costs.push(measure(&context, &same_allocation(81_001, 81_000)));
    }
    eprintln!("same_allocation decision costs: {costs:?}");
    for pair in costs.windows(2) {
        assert!(pair[1].0 <= pair[0].0 * 2, "{costs:?}");
        assert!(pair[1].1 <= pair[0].1 * 2, "{costs:?}");
    }
}

#[test]
fn same_allocation_decision_through_a_chain_is_near_linear() {
    let mut costs = Vec::new();
    for length in [4_u64, 16, 64] {
        let mut context = PureFactContext::new();
        for index in 0..length {
            context = context.assume_proposition(same_allocation(83_000 + index, 83_001 + index));
        }
        costs.push(measure(&context, &same_allocation(83_000, 83_000 + length)));
    }
    eprintln!("same_allocation chain costs: {costs:?}");
    // Each fourfold chain is at most fourfold work, plus a constant.
    for pair in costs.windows(2) {
        assert!(pair[1].0 <= pair[0].0 * 4 + 64, "{costs:?}");
    }
}
