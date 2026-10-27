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

/// Wide facts used to share one global bucket. Both queried bases are
/// aliases admitted after the separation, so selecting their literal blocks
/// alone would lose the witness while filtering the unrelated wide facts.
#[test]
fn wide_separation_lookup_ignores_unrelated_wide_facts() {
    let pointer = |id| Pointer::symbolic(Variable(id));
    let narrow = |base| CMemoryRange::new_with_element_width(base, 0u32.into(), 4u32.into(), 4);
    let wide = |base| {
        CMemoryRange::new_wide(
            base,
            Bitvector32Term::UInt64Constant(0),
            Bitvector32Term::UInt64Constant(8),
            4,
        )
    };
    let separation = |left, right| Proposition::CResourceSeparate {
        left: Box::new(CResource::Memory(left)),
        right: Box::new(CResource::Memory(right)),
    };
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let (left, right) = (pointer(9_990_000), pointer(9_990_001));
        let (left_alias, right_alias) = (pointer(9_990_002), pointer(9_990_003));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_proposition(separation(
                wide(pointer(9_991_000 + index * 2)),
                wide(pointer(9_991_001 + index * 2)),
            ));
        }
        context = context
            .assume_proposition(separation(wide(left.clone()), wide(right.clone())))
            .assume_condition(ConditionTerm::pointer_equal(left_alias.clone(), left), true)
            .assume_condition(
                ConditionTerm::pointer_equal(right_alias.clone(), right),
                true,
            );
        let (answers, work) = crate::instrumentation::measure_deterministic_work(|| {
            (
                context.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                    &narrow(left_alias.clone()),
                    &narrow(right_alias.clone()),
                ),
                context
                    .range_proven_disjoint_from_pointer(&narrow(left_alias.clone()), &right_alias),
                context.ranges_directly_disjoint_from_access(
                    &[narrow(left_alias.clone())],
                    &right_alias,
                    4,
                ),
                context.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                    &wide(pointer(9_990_004)),
                    &wide(pointer(9_990_005)),
                ),
            )
        });
        assert_eq!(answers, (true, true, true, false));
        samples.push(work);
    }
    eprintln!("wide separation query work: {samples:?}");
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 16),
        "wide separation lookup scans unrelated facts: {samples:?}"
    );
}

#[test]
fn wide_separation_lookup_scales_with_its_related_alias_chain() {
    let pointer = |id| Pointer::symbolic(Variable(9_992_000 + id));
    let wide = |base| {
        CMemoryRange::new_wide(
            base,
            Bitvector32Term::UInt64Constant(0),
            Bitvector32Term::UInt64Constant(8),
            4,
        )
    };
    let mut samples = Vec::new();
    for size in [4u64, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let witness = Proposition::CResourceSeparate {
            left: Box::new(CResource::Memory(wide(pointer(0)))),
            right: Box::new(CResource::Memory(wide(pointer(1)))),
        };
        let mut context = PureFactContext::new().assume_proposition(witness);
        for index in 1..=size {
            for side in [0, 1] {
                context = context.assume_condition(
                    ConditionTerm::pointer_equal(
                        pointer(2 * index + side),
                        pointer(2 * (index - 1) + side),
                    ),
                    true,
                );
            }
        }
        let left = CMemoryRange::new_with_element_width(
            pointer(2 * size).offset_by_bytes(4),
            0u32.into(),
            2u32.into(),
            4,
        );
        let right = CMemoryRange::new_with_element_width(
            pointer(2 * size + 1).offset_by_bytes(8),
            0u32.into(),
            2u32.into(),
            4,
        );
        let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                &left, &right,
            )
        });
        assert!(
            proved,
            "translated windows retain their aliased wide witness"
        );
        samples.push(work);
    }
    eprintln!("wide separation alias-chain work: {samples:?}");
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 5 * pair[0] + 32),
        "wide separation query is superlinear in its aliases: {samples:?}"
    );
}
