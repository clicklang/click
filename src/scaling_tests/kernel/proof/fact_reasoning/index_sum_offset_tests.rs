// Scaling regressions for equating offsets by a cited exact index sum.
use super::*;

#[test]
fn an_index_sum_offset_reads_only_the_cited_premise_and_its_own_terms() {
    let _session = VerificationSession::enter();
    let cited = exact_sum();
    // One run first, so term interning is not charged to the first size.
    let facts = crate::kernel::proof::ProofFacts::from_ordered(std::slice::from_ref(&cited));
    normalize_using_conditions(&address_goal(0, 1), std::slice::from_ref(&cited), &facts).unwrap();
    // Unrelated held facts grow; the work stays the same.
    let mut unrelated = Vec::new();
    for size in [8, 32, 128] {
        let mut premises = vec![cited.clone()];
        premises.extend((0..size).map(|id| {
            Proposition::ConditionIs(
                ConditionTerm::integer_equal(
                    observed(993_000 + id),
                    IntegerTerm::add(observed(994_000 + id), observed(995_000 + id)),
                ),
                true,
            )
        }));
        let facts = crate::kernel::proof::ProofFacts::from_ordered(&premises);
        let goal = address_goal(0, 1);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            normalize_using_conditions(&goal, std::slice::from_ref(&cited), &facts)
        });
        result.unwrap();
        unrelated.push(work);
    }
    assert!(unrelated[0] > 0);
    assert!(
        unrelated.iter().all(|work| *work == unrelated[0]),
        "unrelated facts: {unrelated:?}"
    );
    // The offsets both sides share grow; the rule's work grows linearly with
    // them. It is measured alone: the general offset equality that
    // `normalize using` tries first on the same goal has its own curve.
    let mut selected = PureFactContext::new();
    if let Proposition::ConditionIs(condition, value) = &cited {
        selected = selected.assume_condition(condition.clone(), *value);
    }
    let mut shared = Vec::new();
    for size in [4, 16, 64] {
        let Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true) =
            address_goal(size, 1)
        else {
            unreachable!("the goal is a pointer equality");
        };
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            offsets_equal_by_cited_index_sum(&left.offset, &right.offset, &selected)
        });
        assert!(equal);
        shared.push(work);
    }
    assert!(
        shared[1] - shared[0] == (shared[2] - shared[1]) / 4,
        "shared offsets: {shared:?}"
    );
}

#[test]
fn offset_equality_work_is_linear_in_shared_offset_terms() {
    let _session = VerificationSession::enter();
    let mut selected = PureFactContext::new();
    if let Proposition::ConditionIs(condition, value) = exact_sum() {
        selected = selected.assume_condition(condition, value);
    }
    // The pair the general check leaves open, and an unequal one: the same
    // sums with a constant byte added to one side.
    let pairs = |size: u64| {
        let Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true) =
            address_goal(size, 1)
        else {
            unreachable!("the goal is a pointer equality");
        };
        let unequal =
            PointerOffsetTerm::Add(Box::new(right.offset.clone()), Box::new(PointerOffsetTerm::Constant(1)));
        let summed = PointerOffsetTerm::Add(
            Box::new(left.offset.clone()),
            Box::new(PointerOffsetTerm::Constant(0)),
        );
        [(left.offset, right.offset), (summed, unequal)]
    };
    let mut equal_work = Vec::new();
    let mut unequal_work = Vec::new();
    for size in [4, 16, 64] {
        let [equal, unequal] = pairs(size);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::reasoning::memory_resolution::pointer_offsets_equal_for_memory_resolution(
                &equal.0, &equal.1, &selected,
            )
        });
        equal_work.push(work);
        let (decided, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::reasoning::memory_resolution::pointer_offsets_equal_for_memory_resolution(
                &unequal.0, &unequal.1, &selected,
            )
        });
        assert_ne!(decided, Some(true));
        unequal_work.push(work);
    }
    // Shared addends cancel in one linear pass before any rebuild reads
    // them, so four times the shared terms costs at most four times the
    // work; the pairwise cancellation this replaced cost about ten times.
    for work in [&equal_work, &unequal_work] {
        assert!(work[2] <= 4 * work[1], "shared offset terms: {work:?}");
    }
}
