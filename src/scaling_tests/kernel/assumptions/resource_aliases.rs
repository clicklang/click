#[test]
fn read_validity_misses_do_not_walk_pointer_aliases() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer::symbolic(Variable(880_000));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context
                .equality_graph
                .add_equality(&base, &Pointer::symbolic(Variable(880_001 + index)));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert!(!context.has_memory_read_defined_evidence(
                    &CMemory::new(),
                    &base,
                    CType::Int32
                ));
            }
        });
        samples.push(work);
    }
    eprintln!("read validity alias misses: {samples:?}");
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "{samples:?}"
    );
}

#[test]
fn kept_frame_misses_do_not_walk_aliases_or_unrelated_ranges() {
    for aliases in [false, true] {
        let mut samples = Vec::new();
        for size in [8u64, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let pointer = |id| Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(890_000 + id)),
            };
            let query = pointer(0);
            let mut context = PureFactContext::new();
            let mut ranges = ResourceContext::new();
            for index in 1..=size {
                if aliases {
                    context = context.assume_condition(
                        ConditionTerm::pointer_equal(query.clone(), pointer(index)),
                        true,
                    );
                } else {
                    ranges = ranges.unchecked_with_fact(CResourceFact::own_memory(
                        CMemoryRange::new(pointer(index), 0u32.into(), 4u32.into()),
                    ));
                }
            }
            if aliases {
                ranges = ranges.unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                    pointer(1000),
                    0u32.into(),
                    4u32.into(),
                )));
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..4 {
                    assert!(
                        context
                            .kept_range_holding_access(&ranges, || Some(context.clone()), &query, 4)
                            .is_none()
                    );
                }
            });
            samples.push(work);
        }
        eprintln!("kept frame aliases={aliases}: {samples:?}");
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 32),
            "{samples:?}"
        );
    }
}
