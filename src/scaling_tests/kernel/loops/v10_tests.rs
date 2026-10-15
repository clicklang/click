// Scaling tests of `src/kernel/loops.rs` (module `v10_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn loop_view_partition_uses_alias_graph_without_scanning_ambient_ranges() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Pointer::symbolic(Variable(916_100));
    let alias = Pointer::symbolic(Variable(916_101));
    let owner = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
        source.clone(),
        0u32.into(),
        8u32.into(),
        1,
    ));
    let target = Pointer {
        block: source.block.clone(),
        offset: PointerOffsetTerm::Constant(2),
    };
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::pointer_equal(alias.clone(), target), true);
    let spec = CResourceSpec::new(
        CResourceTerm::Memory(
            CMemorySegment::new(c_variable("cursor"), c_int32_literal(0), c_int32_literal(4))
                .with_element_width(1),
        ),
        CResourceAccessMode::View,
        CResourceQuantity::One,
        CResourceTransferRole::Borrow,
        CResourceSnapshot::Entry,
    )
    .unwrap();
    let mut costs = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut resources =
            ResourceContext::new_with_equalities(&assumptions).unchecked_with_fact(owner.clone());
        for index in 0..size {
            resources = resources.unchecked_with_fact(CResourceFact::view_memory(
                CMemoryRange::new_with_element_width(
                    source.clone(),
                    ((index + 1) * 16).into(),
                    ((index + 1) * 16 + 8).into(),
                    1,
                ),
            ));
        }
        resources.synchronize_memory_equalities(&assumptions);
        let state = CState::new()
            .with_local(
                "cursor",
                CValue::typed_pointer(alias.clone(), CType::UInt8Pointer),
            )
            .with_resource_context(resources);
        let (partition, work) = crate::instrumentation::measure_deterministic_work(|| {
            loop_declared_and_withheld_resources(
                &state,
                std::slice::from_ref(&spec),
                &assumptions,
                &mut ExecutionBudget::default(),
            )
            .unwrap()
            .unwrap()
        });
        assert!(partition.1.contains_exact_representation(&owner));
        assert!(partition.0.satisfies_fact(
            &CResourceFact::view_memory(CMemoryRange::new_with_element_width(
                alias.clone(),
                0u32.into(),
                4u32.into(),
                1
            ),),
            &assumptions
        ));
        assert!(
            loop_declared_and_withheld_resources(
                &state,
                std::slice::from_ref(&spec),
                &PureFactContext::new(),
                &mut ExecutionBudget::default()
            )
            .unwrap()
            .is_err()
        );
        costs.push(work);
    }
    assert!(costs.iter().all(|work| *work <= costs[0] * 2), "{costs:?}");
}
