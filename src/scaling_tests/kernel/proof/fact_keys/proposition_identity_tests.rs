// Scaling tests of `src/kernel/proof/fact_keys.rs` (module `proposition_identity_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn alpha_identity_work_scales_with_nested_binder_depth() {
    let make = |depth: u64, offset: u64| {
        let mut proposition = equal(
            Bitvector32Term::Variable(Variable(offset + depth - 1)),
            Bitvector32Term::Constant(1),
        );
        for index in (0..depth).rev() {
            proposition = forall(offset + index, proposition);
        }
        proposition
    };
    let mut work = Vec::new();
    for depth in [8, 16, 32, 64] {
        let left = make(depth, 20_000);
        let right = make(depth, 30_000);
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(propositions_are_alpha_equal(&left, &right));
        });
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(pair[1] <= pair[0] * 3 + 32, "alpha identity work: {work:?}");
    }
}

#[test]
fn local_definedness_identity_ignores_unrelated_store_history() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut samples = Vec::new();
    for size in [8u32, 32, 128, 512] {
        let array = Pointer {
            block: "local:defined-array".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let mut memory = CMemory::new().with_uninitialized_block(array.block.clone(), 4);
        for index in 0..size {
            memory = memory.with_block(format!("local:defined-unrelated-{index}"), 4);
        }
        memory = memory.store(array, CValue::UInt8(7u32.into()));
        let key = proposition_identity_key(&local_definedness_fact(&memory, 82_000)).unwrap();
        for index in 0..size {
            memory = memory.store(
                Pointer {
                    block: format!("local:defined-unrelated-{index}").into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                CValue::Int32(index.into()),
            );
        }
        let goal = local_definedness_fact(&memory, 82_001);
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert_eq!(Some(key.clone()), proposition_identity_key(&goal));
            })
        });
        samples.push((work, map_work));
    }
    assert!(
        samples[3].0 <= samples[0].0 + 8,
        "query walked history: {samples:?}"
    );
    assert!(
        samples[3].1 <= samples[0].1 * 4 + 32,
        "query copied unrelated versions: {samples:?}"
    );
}
