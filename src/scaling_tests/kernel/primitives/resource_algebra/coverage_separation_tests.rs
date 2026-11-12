/// Whether a held range covers a required one is decided by the covering
/// routes alone. A stated separation used to veto every coverage they
/// proved, and asking it walked each separation filed under the ranges'
/// blocks unless their bytes overlapped by constants. A call that reads a
/// symbolic window of a view whose end is symbolic then paid for every
/// separation stated about other windows of that block: in a nested loop of
/// a real proof one call step spent most of its work there. Hold the covered
/// pair fixed and grow those related separations.
#[test]
fn range_coverage_ignores_related_separations() {
    let separation = |left: CMemoryRange, right: CMemoryRange| Proposition::CResourceSeparate {
        left: Box::new(CResource::Memory(left)),
        right: Box::new(CResource::Memory(right)),
    };
    let mut works = Vec::new();
    for size in [16u64, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer::symbolic(Variable(9_889_001));
        let n = MachineTerm::Variable(Variable(9_889_002));
        let count = MachineTerm::Variable(Variable(9_889_003));
        let window = |offset: MachineTerm, length: MachineTerm| {
            CMemoryRange::new_wide(
                base.offset_by_typed_elements(offset, 1, true, true),
                MachineTerm::uint64_constant(0),
                length,
                1,
            )
        };
        let mut facts = PureFactContext::new()
            .assume_condition(
                ConditionTerm::uint64_less_equal(
                    n.clone(),
                    MachineTerm::uint64_constant(i64::MAX as u64),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::uint64_less_equal(count.clone(), n.clone()),
                true,
            );
        for index in 0..size {
            facts = facts.assume_proposition(separation(
                window(
                    MachineTerm::Variable(Variable(9_890_000 + index)),
                    MachineTerm::uint64_constant(8),
                ),
                CMemoryRange::new_wide(
                    Pointer::symbolic(Variable(9_891_000 + index)),
                    MachineTerm::uint64_constant(0),
                    MachineTerm::uint64_constant(8),
                    1,
                ),
            ));
        }
        let held =
            CMemoryRange::new_wide(base.clone(), MachineTerm::uint64_constant(0), n.clone(), 1);
        let read = window(
            MachineTerm::uint64_subtract(n.clone(), count.clone()),
            count,
        );
        let (covered, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory_range_covers(&held, &read, &facts)
        });
        assert!(covered, "the held range covers the read at size {size}");
        works.push((size, work));
    }
    let (_, first) = works[0];
    for &(size, work) in &works[1..] {
        assert!(
            work <= first + 16,
            "coverage grows with related separations at {size}: {works:?}"
        );
    }
}
