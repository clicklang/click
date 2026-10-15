// Scaling tests of `src/kernel/functions.rs` (module `counted_membership_framing_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn independent_body_expansion_indexes_definitions_and_walks_depth_once() {
    let pointer = Pointer {
        block: "counter".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let assumptions = PureFactContext::new();
    let memory = CMemory::new().with_block("counter", 4);
    let ordinary = |name: String, next: Option<String>| {
        CCompositeResourceDefinition::new(
            name,
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            next.into_iter()
                .map(|next| {
                    CResourceSpec::composite(
                        CResourceAccessMode::Own,
                        next,
                        vec![c_variable("p")],
                        vec![CType::Int32Pointer],
                    )
                })
                .collect(),
            vec![],
        )
    };
    let population = || {
        CCompositeResourceDefinition::authority_control(
            "z-count",
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            vec![CResourceSpec::owned_memory(CMemorySegment::new(
                c_variable("p"),
                c_int32_literal(0),
                c_int32_literal(1),
            ))],
            vec![],
        )
    };
    let root = |name: &str| {
        ResourceContext::new().unchecked_with_fact(CResourceFact::own_composite(
            name.into(),
            vec![CValue::pointer(pointer.clone())],
        ))
    };
    let mut depth_samples = Vec::new();
    for depth in [16, 32, 64] {
        let mut definitions = (0..depth)
            .map(|index| {
                ordinary(
                    format!("wrapper-{index:04}"),
                    Some(if index + 1 == depth {
                        "z-count".into()
                    } else {
                        format!("wrapper-{:04}", index + 1)
                    }),
                )
            })
            .collect::<Vec<_>>();
        definitions.push(population());
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let expanded = expand_composites_for_frame(
                &root("wrapper-0000"),
                &definitions,
                &memory,
                &assumptions,
            )
            .unwrap();
            assert!(owned_memory_ranges_of(&expanded).is_empty());
            assert_eq!(expanded.facts().len(), 1);
        });
        depth_samples.push(work);
    }
    assert!(
        depth_samples[2] <= depth_samples[0] * 7 + 128,
        "nested expansion rescans its ancestors: {depth_samples:?}"
    );
    let mut frame_samples = Vec::new();
    for size in [16, 64, 256] {
        let mut definitions = (0..size)
            .map(|index| ordinary(format!("unrelated-{index:04}"), None))
            .collect::<Vec<_>>();
        definitions.push(population());
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let expanded =
                expand_composites_for_frame(&root("z-count"), &definitions, &memory, &assumptions)
                    .unwrap();
            assert!(owned_memory_ranges_of(&expanded).is_empty());
        });
        frame_samples.push(work);
    }
    for pair in frame_samples.windows(2) {
        assert!(
            pair[1] <= pair[0] * 2 + 16,
            "selected body scans unrelated definitions: {frame_samples:?}"
        );
    }
}
