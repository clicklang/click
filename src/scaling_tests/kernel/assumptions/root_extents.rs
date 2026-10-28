use super::*;

fn extent_work(steps: u64, unrelated: u64) -> usize {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer {
        block: PointerBlock::Heap(982_000),
        offset: PointerOffsetTerm::Constant(0),
    };
    let held = CMemoryRange::new(base.clone(), 0u32.into(), 8u32.into());
    let mut previous = CPointerValue::new(base, CType::Int32Pointer);
    let mut facts = PureFactContext::new();
    for i in 0..unrelated {
        facts = facts.assume_condition(
            ConditionTerm::pointer_value_equal(
                read_pointer(983_000 + 2 * i),
                read_pointer(983_001 + 2 * i),
            ),
            true,
        );
    }
    let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
        for i in 0..steps {
            let next = read_pointer(984_000 + i);
            facts = facts.assume_condition(
                ConditionTerm::pointer_value_equal(next.clone(), previous),
                true,
            );
            assert!(facts.access_designations_match(next.access_designation(), &held));
            previous = next;
        }
    });
    work
}

#[test]
fn root_extent_checks_use_class_keys_across_growing_aliases() {
    let unrelated = [0, 8, 16, 64].map(|n| extent_work(4, n));
    assert!(
        unrelated.iter().all(|w| *w <= unrelated[0] + 32),
        "{unrelated:?}"
    );
    let growing = [4, 8, 16, 32].map(|n| extent_work(n, 16));
    assert!(growing[0] > 0);
    assert!(growing.windows(2).all(|p| p[1] <= 3 * p[0]), "{growing:?}");
}
