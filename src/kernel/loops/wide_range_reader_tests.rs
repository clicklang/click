use super::*;
// Validated loop frames and call summaries retain native bounds; the
// signed run optimization must fall back when it sees one.
#[test]
fn wide_loop_frames_cover_native_accesses_and_refuse_cross_width_ranges() {
    let base = Pointer::symbolic(Variable(984_500));
    let wide = CMemoryRange::new_wide(
        base.clone(),
        Bitvector32Term::UInt64Constant(0),
        Bitvector32Term::UInt64Constant(1 << 33),
        4,
    );
    let segment = EvaluatedMemorySegment {
        designation: wide.designation.clone(),
        opaque_extent: wide.opaque_extent.clone(),
        extent_known: wide.carrier_extent_known,
        base: base.clone(),
        start: wide.bound_terms().0.clone(),
        end: wide.bound_terms().1.clone(),
        element_width: 4,
        kind: RangeIndexKind::UInt64,
        base_designations: [None, None],
        formation_coverage: Default::default(),
    };
    let facts = PureFactContext::new();
    assert!(loop_effect_segment_contains_range(&segment, &wide, &facts));
    assert!(loop_effect_segment_contains_pointer(
        &segment, &base, 4, &facts
    ));
    let bytes = CMemoryRange::new_wide(
        base.clone(),
        Bitvector32Term::UInt64Constant(0),
        Bitvector32Term::UInt64Constant(1 << 33),
        1,
    );
    assert!(!loop_effect_segment_contains_range(
        &segment, &bytes, &facts
    ));
    let check = CLoopEffectCheck::new(CLoopEffect::Mutable(vec![]), None)
        .with_validated_ranges(vec![wide.clone()]);
    let state = CState::new();
    let mut budget = ExecutionBudget::beside_live_state();
    assert!(
        collect_loop_effect_check_obligations(
            &state,
            &state,
            &[check],
            &ExecutionFacts::new(),
            &[],
            &facts,
            &mut budget
        )
        .unwrap()
        .is_empty()
    );
    let summary = Proposition::CMemoryEffectSummary {
        before: state.memory().clone(),
        after: state.memory().clone(),
        mutable_ranges: vec![wide],
    };
    let run = crate::kernel::primitives::CellRun::new(
        base,
        4,
        CType::Int32,
        4,
        state.memory().clone().into(),
        crate::kernel::primitives::IndexIntervals::default(),
    );
    assert!(run_slots_clear_of_loop_summaries(&run, &[summary], &facts).is_none());
}
