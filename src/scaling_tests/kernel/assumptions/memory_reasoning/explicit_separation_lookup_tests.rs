// Scaling tests of `src/kernel/assumptions/memory_reasoning.rs` (module `explicit_separation_lookup_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

/// Whether two ranges are disjoint by a stated separation reads only the
/// separations filed under the blocks related to the queried bases. A wide
/// queried range and a base reached through a proven equality once scanned
/// every separation, so unrelated separations made each query linear in
/// their number.
#[test]
fn explicit_separation_lookup_reads_only_related_blocks() {
    let pointer = |id| Pointer::symbolic(Variable(id));
    let narrow =
        |base: Pointer| CMemoryRange::new_with_element_width(base, 0u32.into(), 8u32.into(), 1);
    let wide = |base: Pointer| CMemoryRange::new_wide(base, 0u32.into(), 8u32.into(), 1);
    let separation = |left: CMemoryRange, right: CMemoryRange| Proposition::CResourceSeparate {
        left: Box::new(CResource::Memory(left)),
        right: Box::new(CResource::Memory(right)),
    };
    let mut works = Vec::new();
    for size in [16u64, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let model = pointer(9_887_001);
        let alias = pointer(9_887_002);
        let node = pointer(9_887_003);
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_proposition(separation(
                narrow(pointer(9_888_000 + 2 * index)),
                narrow(pointer(9_888_001 + 2 * index)),
            ));
        }
        context =
            context.assume_proposition(separation(narrow(model.clone()), narrow(node.clone())));
        context =
            context.assume_condition(ConditionTerm::pointer_equal(alias.clone(), model), true);
        let (separate, separate_work) = crate::instrumentation::measure_deterministic_work(|| {
            context.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                &narrow(alias.clone()),
                &narrow(node.clone()),
            )
        });
        assert!(
            separate,
            "the separation reaches the alias through its base equality"
        );
        let (unrelated, unrelated_work) =
            crate::instrumentation::measure_deterministic_work(|| {
                context.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                    &wide(pointer(9_887_004)),
                    &narrow(pointer(9_887_005)),
                )
            });
        assert!(!unrelated, "no separation covers unrelated ranges");
        works.push((size, separate_work, unrelated_work));
    }
    let (_, first_separate, first_unrelated) = works[0];
    for &(size, separate, unrelated) in &works[1..] {
        assert!(
            separate <= first_separate + 16 && unrelated <= first_unrelated + 16,
            "the lookup grows with unrelated separations at {size}: {works:?}"
        );
    }
}
