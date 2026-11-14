// Scaling tests of `src/kernel/primitives/resource_algebra.rs` (module `support_removal_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn frame_exchange_preserves_occurrences_and_does_not_scan_unrelated_frame() {
    let assumptions = PureFactContext::new();
    let before = ResourceFact::own_composite("before".into(), Vec::new());
    let after = ResourceFact::own_composite("after".into(), Vec::new());
    let body = ResourceContext::new().unchecked_with_fact(before.clone());
    let exit = body
        .clone()
        .without_exact_representation(&before)
        .unwrap()
        .unchecked_with_fact(after.clone());
    let occurrence = exit.unique_owned_occurrence_for_fact(&after).unwrap();
    let mut measurements = Vec::new();
    for size in [8, 32, 128] {
        let mut frame = body.clone();
        for index in 0..size {
            frame = frame.unchecked_with_fact(ResourceFact::own_composite(
                format!("frame_{index}"),
                Vec::new(),
            ));
        }
        let (restored, work) = crate::instrumentation::measure_deterministic_work(|| {
            exit.restore_frame_after_exchange(&body, &frame, &assumptions)
                .unwrap()
        });
        assert!(!restored.contains_exact_representation(&before));
        assert_eq!(
            restored.unique_owned_occurrence_for_fact(&after),
            Some(occurrence)
        );
        assert_eq!(restored.facts().len(), size + 1);
        measurements.push(work);
    }
    assert!(
        measurements.iter().all(|work| *work == measurements[0]),
        "{measurements:?}"
    );
}

#[test]
fn constructed_exchange_preserves_support_and_scales_with_delta() {
    let before_fact = ResourceFact::own_composite("before".into(), Vec::new());
    let after_fact = ResourceFact::own_composite("after".into(), Vec::new());
    let view = ResourceFact::view_token("body".into(), Vec::new());
    let before = ResourceContext::new().unchecked_with_fact(before_fact.clone());
    let after = before
        .clone()
        .without_exact_representation(&before_fact)
        .unwrap()
        .unchecked_with_fact(after_fact.clone())
        .unchecked_with_supported_facts(&after_fact, vec![view.clone()])
        .with_cached_supported_expansion(&after_fact, vec![view.clone()]);
    let mut samples = Vec::new();
    for size in [8, 32, 128] {
        let mut frame = before.clone();
        for index in 0..size {
            frame = frame.unchecked_with_fact(ResourceFact::own_composite(
                format!("unrelated_{index}"),
                Vec::new(),
            ));
        }
        let (retained, work) = crate::instrumentation::measure_deterministic_work(|| {
            frame.with_constructed_exchange(&before, &after).unwrap()
        });
        samples.push(work);
        assert_eq!(retained.facts().len(), size + 2);
        assert_eq!(
            retained.unique_owned_occurrence_for_fact(&after_fact),
            after.unique_owned_occurrence_for_fact(&after_fact)
        );
        assert_eq!(
            retained.cached_supported_expansion(&after_fact),
            Some([view.clone()].as_slice())
        );
        let restored = retained.with_constructed_exchange(&after, &before).unwrap();
        assert_eq!(restored.facts().len(), size + 1);
        assert!(restored.contains_exact_representation(&before_fact));
        assert!(!restored.contains_exact_representation(&view));
        assert_eq!(restored.cached_supported_expansion(&after_fact), None);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "{samples:?}"
    );
}

#[test]
fn a_resource_delta_refusal_does_not_walk_the_shared_past() {
    let costs = [4, 16, 64, 256].map(|history| {
        let mut shared = ResourceContext::new();
        for index in 0..history {
            shared = shared
                .unchecked_with_fact(ResourceFact::own_token(format!("past_{index}"), Vec::new()));
        }
        let left = shared
            .clone()
            .unchecked_with_fact(ResourceFact::own_token("left".into(), Vec::new()));
        let right = shared.unchecked_with_fact(ResourceFact::own_token("right".into(), Vec::new()));
        let (changed, cost) =
            crate::instrumentation::measure_deterministic_work(|| right.changed_facts_since(&left));
        assert!(changed.is_none());
        cost
    });
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}

#[test]
fn returned_symbolic_cell_rejoins_without_scanning_unrelated_ownership() {
    let mut samples = Vec::new();
    for size in [4_u64, 16, 64, 256] {
        let base = Pointer::symbolic(Variable(987_400));
        let index = MachineTerm::Variable(Variable(987_401));
        let middle = MachineTerm::add(index.clone(), 1u32.into());
        let end = MachineTerm::add(index.clone(), 2u32.into());
        let range = |base, start, end| {
            ResourceFact::own_memory(MemoryRange::new_with_element_width(base, start, end, 4))
        };
        let facts = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_equal(0u32.into(), index.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(index.clone(), 100u32.into()),
                true,
            );
        let mut resources = ResourceContext::new_with_equalities(&facts);
        for item in 0..size {
            resources = resources.unchecked_with_fact(range(
                Pointer::symbolic(Variable(988_000 + item)),
                0u32.into(),
                2u32.into(),
            ));
        }
        let cell = range(
            base.offset_by_elements(index.clone(), 4),
            0u32.into(),
            1u32.into(),
        );
        let remainder = range(base.clone(), middle, end.clone());
        resources = resources
            .unchecked_with_fact(cell.clone())
            .unchecked_with_fact(remainder);
        resources.synchronize_memory_equalities(&facts);
        let required = range(base, index, end);
        let (consumed, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources
                .clone()
                .without_fact_incrementally(&required, &facts)
        });
        let consumed = consumed.expect("the returned cell and adjacent residue rejoin");
        assert_eq!(consumed.facts().len(), size as usize);
        // Consumption forks the resource context; the original retains the cell.
        assert!(resources.contains_exact_representation(&cell));
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "{samples:?}"
    );
}

#[test]
fn shared_pointer_load_footprints_keep_depth_refusal_without_tree_expansion() {
    use crate::kernel::{
        KernelTerm, KernelTermExport, MachineOperandView as V, SharedMachineIntegerTerm as S,
    };
    let mut costs = Vec::new();
    for depth in [8, 16, 32, 65] {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Pointer::symbolic(Variable(1081401));
        let memory = crate::kernel::intern_memory(
            Memory::new().store(address.clone(), crate::kernel::int32(7)),
        );
        let load = MachineTerm::MemoryLoad(
            memory,
            Box::new(address.clone()),
            crate::kernel::LoadKind::Int32,
        );
        let mut root =
            KernelTerm::retained_machine_operand(MachineIntegerType::Int32, V::Legacy(&load));
        for _ in 0..depth {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
        }
        let offset = PointerOffsetTerm::Int32Scaled {
            value: S::from_shared(MachineIntegerType::Int32, root).unwrap(),
            byte_width: 4,
        };
        let exports = KernelTermExport::machine_export_count();
        let mut ranges = Vec::new();
        let mut uncertain = false;
        let (_, cost) = crate::instrumentation::measure_deterministic_work(|| {
            collect_memory_load_ranges(&offset, &mut ranges, &mut uncertain, &mut None)
        });
        assert_eq!(uncertain, depth >= MAX_MEMORY_LOAD_FOOTPRINT_DEPTH);
        if !uncertain {
            assert_eq!(ranges.len(), 1);
            assert_eq!(ranges[0].base(), &address);
            assert_eq!(ranges[0].element_width(), 4);
        }
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        costs.push(cost);
    }
    for pair in costs.windows(2) {
        assert!(pair[1] <= pair[0] * 3 + 10, "{costs:?}");
    }
}
