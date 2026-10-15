use super::*;

fn outside(owned: Vec<CMemoryRange>, required: CMemoryRange) -> Vec<StorageWriteOutsideFootprint> {
    let function = CFunction::new(
        CType::Int32,
        "caller",
        Vec::new(),
        c_return(c_int32_literal(0)),
    );
    let memory = CMemory::new();
    let facts = [
        ExecutionPureFact::internal(Proposition::CMemoryEffectSummary {
            before: memory.clone(),
            after: memory,
            mutable_ranges: vec![required],
        })
        .into_certified(),
    ];
    let projection = CFunctionMemoryEffectProjection {
        ranges: owned,
        evidence_facts: ExecutionFacts::new(),
        range_sources: Vec::new(),
    };
    storage_writes_outside_owned_footprint(
        &function,
        &CState::new(),
        &facts,
        &PureFactContext::new(),
        None,
        Some(&projection),
    )
    .unwrap()
    .unwrap()
}

#[test]
fn storage_summary_combines_adjacent_owned_fields() {
    for base in [
        CMemory::global_pointer("pair"),
        CMemory::static_pointer("caller", "pair"),
    ] {
        let left = CMemoryRange::new_with_element_width(base.clone(), 0.into(), 1.into(), 8);
        let right =
            CMemoryRange::new_with_element_width(base.offset_by_bytes(8), 0.into(), 1.into(), 8);
        let required = CMemoryRange::new_with_element_width(base.clone(), 0.into(), 4.into(), 4);
        assert!(outside(vec![left.clone(), right.clone()], required.clone()).is_empty());
        assert!(outside(vec![right, left], required).is_empty());
        let interior = CMemoryRange::new_with_element_width(base.clone(), 1.into(), 3.into(), 4);
        let owned = CMemoryRange::new_with_element_width(base, 0.into(), 2.into(), 8);
        assert!(outside(vec![owned], interior).is_empty());
    }
}

#[test]
fn storage_summary_does_not_fill_gaps_or_cross_storage_blocks() {
    let base = CMemory::global_pointer("pair");
    let left = CMemoryRange::new_with_element_width(base.clone(), 0.into(), 1.into(), 8);
    let right =
        CMemoryRange::new_with_element_width(base.offset_by_bytes(8), 0.into(), 1.into(), 8);
    let required = CMemoryRange::new_with_element_width(base.clone(), 0.into(), 4.into(), 4);
    let suffix =
        CMemoryRange::new_with_element_width(base.offset_by_bytes(12), 0.into(), 1.into(), 4);
    let other = CMemoryRange::new_with_element_width(
        CMemory::global_pointer("other"),
        0.into(),
        1.into(),
        8,
    );
    for owned in [
        vec![],
        vec![left.clone()],
        vec![left.clone(), left.clone()],
        vec![left.clone(), left.clone(), suffix],
        vec![left.clone(), other],
    ] {
        assert_eq!(outside(owned, required.clone()).len(), 1);
    }
    let larger = CMemoryRange::new_with_element_width(base, 0.into(), 5.into(), 4);
    assert_eq!(outside(vec![left, right], larger).len(), 1);
}
