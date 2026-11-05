#[test]
fn disjoint_write_range_visits_are_charged_even_for_distinct_blocks() {
    let pointer = Pointer {
        block: "local:read".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let assumptions = PureFactContext::new();
    for size in [1usize, 8, 32, 64] {
        let ranges: Vec<_> = (0..size)
            .map(|index| {
                CMemoryRange::new_with_element_width(
                    Pointer {
                        block: format!("local:write-{index}").into(),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    0u32.into(),
                    4u32.into(),
                    1,
                )
            })
            .collect();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                assert!(
                    typed_ranges_disjoint_from_pointer_evidence(&ranges, &pointer, 4, &assumptions)
                        .is_some()
                );
            }
        });
        assert_eq!(
            work,
            size * size,
            "each query must charge each visited range"
        );
        let (_, one_query) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(
                typed_ranges_disjoint_from_pointer_evidence(&ranges, &pointer, 4, &assumptions)
                    .is_some()
            );
        });
        assert_eq!(one_query, size);
    }
    let overlapping =
        CMemoryRange::new_with_element_width(pointer.clone(), 0u32.into(), 4u32.into(), 1);
    let refusal_work = |size| {
        crate::instrumentation::measure_deterministic_work(|| {
            assert!(
                typed_ranges_disjoint_from_pointer_evidence(
                    &vec![overlapping.clone(); size],
                    &pointer,
                    4,
                    &assumptions
                )
                .is_none()
            );
        })
        .1
    };
    assert_eq!(
        refusal_work(1),
        refusal_work(64),
        "a refusal must not charge unvisited ranges"
    );
}
