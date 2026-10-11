use super::*;

fn range(base: Pointer, end: u32, width: u32) -> CMemoryRange {
    CMemoryRange::new_with_element_width(base, 0u32.into(), end.into(), width)
}

#[test]
fn separated_access_selection_keeps_original_and_exact_alias_buckets() {
    let _session = crate::kernel::VerificationSession::enter();
    let write = Pointer::symbolic(Variable(9_880_110));
    let concrete = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(9_880_111)),
    };
    let field = Pointer::symbolic(Variable(9_880_112));
    let alias = Proposition::ConditionIs(
        ConditionTerm::pointer_equal(write.clone(), concrete.clone()),
        true,
    );
    let step = CMemoryDerivation::Store {
        base: intern_c_memory(CMemory::new()),
        pointer: write.clone(),
        value: CValue::Int32(7u32.into()),
    };
    // Separation may be stated in either exact spelling. Neither bucket can
    // replace the other, and every selected side must cover the complete read.
    for base in [write.clone(), concrete.clone()] {
        let separation = Proposition::CResourceSeparate {
            left: Box::new(CResource::Memory(range(base, 1, 4))),
            right: Box::new(CResource::Memory(range(field.clone(), 1, 8))),
        };
        let assumptions = PureFactContext::new()
            .assume_proposition(alias.clone())
            .assume_proposition(separation.clone());
        let proof = typed_store_separated_ranges_evidence(&write, 4, &field, 8, &assumptions)
            .expect("both exact spellings retain full-width separation");
        assert!(proof.checks(&step, &field, 8, &assumptions));
        assert!(!proof.checks(&step, &field, 16, &assumptions));
        assert!(!proof.checks(
            &step,
            &field,
            8,
            &assumptions.without_exact_fact(&separation)
        ));
    }
    let owned = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(range(concrete, 1, 4)))
        .unchecked_with_fact(CResourceFact::own_memory(range(field.clone(), 1, 8)));
    let assumptions = PureFactContext::new()
        .assume_proposition(alias.clone())
        .assume_proposition(Proposition::CResourceComposition(owned));
    let proof = typed_store_separated_ranges_evidence(&write, 4, &field, 8, &assumptions)
        .expect("an exact alias selects the composition's owned bucket");
    assert!(proof.checks(&step, &field, 8, &assumptions));
    assert!(!proof.checks(&step, &field, 8, &assumptions.without_exact_fact(&alias)));
}

#[test]
fn store_separation_without_authority_does_not_resolve_load_histories() {
    let mut samples = Vec::new();
    for count in [16, 128, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let at = |id| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(id)),
        };
        let mut memory = CMemory::new();
        for i in 0..count {
            memory = memory.store(at(9_885_000 + i), CValue::Int32((i as u32).into()));
        }
        let snapshot = intern_c_memory(memory);
        let selected = |id| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(
                Bitvector32Term::MemoryLoad(
                    snapshot.clone(),
                    Box::new(at(id)),
                    crate::kernel::LoadKind::Bits32,
                ),
                4,
            ),
        };
        let write = selected(9_884_001);
        let load = selected(9_884_002);
        // Without an indexed partition candidate, neither load's history can
        // supply the missing authority. Refuse before comparing their values.
        let (proof, work) = crate::instrumentation::measure_deterministic_work(|| {
            typed_store_separated_ranges_evidence(&write, 4, &load, 4, &PureFactContext::new())
        });
        assert!(proof.is_none());
        // A candidate whose write side is too narrow must also refuse before
        // asking whether this history-derived read fits its other side. The
        // reversed orientation cannot hold the write at offset zero either.
        let write = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let read_base = write.offset_by_bytes(32);
        let partial = PureFactContext::new().assume_proposition(Proposition::CResourceSeparate {
            left: Box::new(CResource::Memory(range(write.clone(), 1, 1))),
            right: Box::new(CResource::Memory(range(read_base, 1, 4))),
        });
        let (proof, partial_work) = crate::instrumentation::measure_deterministic_work(|| {
            typed_store_separated_ranges_evidence(&write, 4, &load, 4, &partial)
        });
        assert!(proof.is_none());
        samples.push((work, partial_work));
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "missing partition authority resolved unrelated store histories: {samples:?}"
    );
}

#[test]
fn selected_store_composition_rejects_a_later_transitive_alias() {
    let _session = crate::kernel::VerificationSession::enter();
    let write = Pointer::symbolic(Variable(9_884_010));
    let load = Pointer::symbolic(Variable(9_884_011));
    let bridge = Pointer::symbolic(Variable(9_884_012));
    let owned = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(range(write.clone(), 1, 4)))
        .unchecked_with_fact(CResourceFact::own_memory(range(load.clone(), 1, 8)));
    let entry = PureFactContext::new().assume_proposition(Proposition::CResourceComposition(owned));
    let retained = typed_store_separated_ranges_evidence(&write, 4, &load, 8, &entry)
        .expect("the selected composition initially covers both complete accesses");
    let step = CMemoryDerivation::Store {
        base: intern_c_memory(CMemory::new()),
        pointer: write.clone(),
        value: CValue::Int32(7u32.into()),
    };
    assert!(retained.checks(&step, &load, 8, &entry));
    let aliased = entry
        .assume_condition(
            ConditionTerm::pointer_equal(write.clone(), bridge.clone()),
            true,
        )
        .assume_condition(ConditionTerm::pointer_equal(bridge, load.clone()), true);
    assert_eq!(
        aliased.exact_condition_value(&ConditionTerm::pointer_equal(write.clone(), load.clone())),
        None,
        "the selected addresses are related through a bridge, not an exact fact"
    );
    assert!(typed_store_separated_ranges_evidence(&write, 4, &load, 8, &aliased).is_none());
    assert!(!retained.checks(&step, &load, 8, &aliased));
}

#[test]
fn equivalent_base_membership_retains_its_checked_equality() {
    use crate::kernel::resource_tracker::cell_source::PointerInRangeEvidence;
    use crate::kernel::{IntegerTerm, MachineIntegerType};
    let _session = crate::kernel::VerificationSession::enter();
    let wide = Bitvector32Term::Variable(Variable(9_895_010));
    let narrow = Bitvector32Term::Variable(Variable(9_895_011));
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(narrow.clone(), 4),
    };
    let selected = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::add(
            PointerOffsetTerm::scale_int64(wide.clone(), 4, true),
            PointerOffsetTerm::Constant(4),
        ),
    };
    let range = range(base, 2, 4);
    let equality = Proposition::ConditionIs(
        ConditionTerm::IntegerEqual(
            IntegerTerm::from_machine(MachineIntegerType::UInt64, wide)
                .unwrap()
                .into(),
            IntegerTerm::from_machine(MachineIntegerType::Int32, narrow)
                .unwrap()
                .into(),
        ),
        true,
    );
    let checked = PureFactContext::new().assume_proposition(equality.clone());
    let proof = PointerInRangeEvidence::for_pointer(&selected, &range, &checked)
        .expect("the exact native observations authenticate the alternate base");
    assert!(matches!(
        &proof,
        PointerInRangeEvidence::EquivalentBase { .. }
    ));
    assert!(proof.checks(&selected, &range, &checked));
    let withdrawn = checked.without_exact_fact(&equality);
    assert!(!proof.checks(&selected, &range, &withdrawn));
    assert!(PointerInRangeEvidence::for_pointer(&selected, &range, &withdrawn).is_none());
    let outside =
        CMemoryRange::new_with_element_width(range.base().clone(), 0u32.into(), 1u32.into(), 4);
    assert!(!proof.checks(&selected, &outside, &checked));
}

#[test]
fn symbolic_range_end_retains_nonwrapping_full_span_separation() {
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let n = Bitvector32Term::Variable(Variable(9_880_120));
    let written = CMemoryRange::new(base.clone(), 0u32.into(), n.clone());
    let pointer = base.offset_by_elements(n.clone(), 4);
    let nonnegative =
        Proposition::ConditionIs(ConditionTerm::signed_less_equal(0u32.into(), n), true);
    let assumptions = PureFactContext::new().assume_proposition(nonnegative.clone());
    let proof = typed_range_disjoint_from_pointer_evidence(&written, &pointer, 8, &assumptions)
        .expect("an exact endpoint is after all bytes of the nonwrapping range");
    assert!(proof.checks(&written, &pointer, 8, &assumptions));
    assert!(proof.checks(&written, &pointer, 16, &assumptions));
    assert!(!proof.checks(
        &written,
        &pointer,
        8,
        &assumptions.without_exact_fact(&nonnegative)
    ));
    assert!(
        typed_range_disjoint_from_pointer_evidence(&written, &pointer, 8, &PureFactContext::new())
            .is_none()
    );
    let wrapped = CMemoryRange::new(
        base.clone(),
        (i32::MAX as u32).into(),
        (i32::MIN as u32).into(),
    );
    let wrapped_end = base.offset_by_elements((i32::MIN as u32).into(), 4);
    assert!(
        RangeDisjointFromPointerEvidence::for_after_end(&wrapped, &wrapped_end, 4, &assumptions)
            .is_none()
    );
    let later = CMemoryRange::new(base.clone(), 1u32.into(), 2u32.into());
    assert!(typed_range_disjoint_from_pointer_evidence(&later, &base, 4, &assumptions).is_some());
    assert!(typed_range_disjoint_from_pointer_evidence(&later, &base, 8, &assumptions).is_none());
}

#[test]
fn symbolic_range_end_selection_ignores_unrelated_order_facts() {
    let mut samples = Vec::new();
    for count in [16, 128, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let n = Bitvector32Term::Variable(Variable(9_880_130));
        let written = CMemoryRange::new(base.clone(), 0u32.into(), n.clone());
        let pointer = base.offset_by_elements(n.clone(), 4);
        // The selected endpoint edge 1 <= n also proves 0 <= n. It must
        // check its exact premise and the intrinsic constant connection.
        let positive =
            Proposition::ConditionIs(ConditionTerm::signed_less_equal(1u32.into(), n), true);
        let mut assumptions = PureFactContext::new().assume_proposition(positive.clone());
        for i in 0..count {
            assumptions = assumptions.assume_proposition(Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(
                    Bitvector32Term::Variable(Variable(9_881_000 + i * 2)),
                    Bitvector32Term::Variable(Variable(9_881_001 + i * 2)),
                ),
                true,
            ));
        }
        let (proof, work) = crate::instrumentation::measure_deterministic_work(|| {
            let proof =
                typed_range_disjoint_from_pointer_evidence(&written, &pointer, 8, &assumptions)
                    .unwrap();
            assert!(proof.checks(&written, &pointer, 8, &assumptions));
            proof
        });
        assert!(!proof.checks(
            &written,
            &pointer,
            8,
            &assumptions.without_exact_fact(&positive)
        ));
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "unrelated order facts changed selected range-end work: {samples:?}"
    );
}

#[test]
fn bounded_child_range_retains_symbolic_parent_extent() {
    let owner = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(9_880_140)), 4),
    };
    let data = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(9_880_141)), 4),
    };
    let n = Bitvector32Term::Variable(Variable(9_880_142));
    let parent = CMemoryRange::new(data.clone(), 0u32.into(), n.clone());
    let written = range(data.clone(), 1, 4);
    let field = owner.offset_by_bytes(8);
    let separation = Proposition::CResourceSeparate {
        left: Box::new(CResource::Memory(range(owner, 6, 4))),
        right: Box::new(CResource::Memory(parent)),
    };
    let bound = Proposition::ConditionIs(ConditionTerm::signed_less_equal(1u32.into(), n), true);
    let assumptions = PureFactContext::new()
        .assume_proposition(separation)
        .assume_proposition(bound.clone());
    let proof = typed_range_disjoint_from_pointer_evidence(&written, &field, 8, &assumptions)
        .expect("the complete one-element write fits its bounded parent");
    assert!(proof.checks(&written, &field, 8, &assumptions));
    assert!(!proof.checks(&written, &field, 8, &assumptions.without_exact_fact(&bound)));
    let wider = range(data.clone(), 2, 4);
    assert!(!proof.checks(&wider, &field, 8, &assumptions));
    assert!(typed_range_disjoint_from_pointer_evidence(&wider, &field, 8, &assumptions).is_none());
    let symbolic_extent = Bitvector32Term::Variable(Variable(9_880_143));
    let wrapped_parent = CMemoryRange::new(
        data.offset_by_elements((i32::MAX as u32).into(), 4),
        0u32.into(),
        symbolic_extent.clone(),
    );
    let wrapped_child = CMemoryRange::new(
        data.clone(),
        (i32::MAX as u32).into(),
        (i32::MIN as u32).into(),
    );
    let wrapped_assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::signed_less_equal(1u32.into(), symbolic_extent),
        true,
    );
    assert!(
        RangeInRangeEvidence::for_range(&wrapped_child, &wrapped_parent, &wrapped_assumptions)
            .is_none()
    );
    let wide = CMemoryRange::new_wide(
        data,
        Bitvector32Term::UInt64Constant(0),
        Bitvector32Term::UInt64Constant(1),
        4,
    );
    assert!(!proof.checks(&wide, &field, 8, &assumptions));
    assert!(typed_range_disjoint_from_pointer_evidence(&wide, &field, 8, &assumptions).is_none());
}

#[test]
fn successor_guard_frames_complete_indexed_reads_in_separate_arrays() {
    let _session = crate::kernel::VerificationSession::enter();
    let i = Bitvector32Term::Variable(Variable(9_887_100));
    let k = Bitvector32Term::Variable(Variable(9_887_101));
    let n = Bitvector32Term::Variable(Variable(9_887_102));
    let capacity = Bitvector32Term::Variable(Variable(9_887_103));
    let dst = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(9_887_104)), 4),
    };
    let src = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(9_887_105)), 4),
    };
    let dst_range = CMemoryRange::new(dst.clone(), 0u32.into(), capacity.clone());
    let src_range = CMemoryRange::new(src.clone(), 0u32.into(), capacity.clone());
    let mut facts = PureFactContext::new().assume_proposition(Proposition::CResourceSeparate {
        left: Box::new(CResource::Memory(dst_range)),
        right: Box::new(CResource::Memory(src_range)),
    });
    let lower = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(0u32.into(), k.clone()),
        true,
    );
    let upper = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(k.clone(), Bitvector32Term::add(i.clone(), 1u32.into())),
        true,
    );
    let bounds = [
        lower.clone(),
        upper.clone(),
        Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(0u32.into(), i.clone()),
            true,
        ),
        Proposition::ConditionIs(ConditionTerm::signed_less_than(i.clone(), n.clone()), true),
        Proposition::ConditionIs(ConditionTerm::signed_less_equal(n.clone(), capacity), true),
    ];
    for fact in &bounds {
        facts = facts.assume_proposition(fact.clone());
    }
    let write = dst.offset_by_elements(i, 4);
    let read = src.offset_by_elements(k, 4);
    let (proof, premises) = crate::kernel::collect_reasoning_provenance(|| {
        crate::kernel::capture_implicit_reasoning_provenance(|| {
            typed_store_separated_ranges_evidence(&write, 4, &read, 4, &facts)
        })
    });
    let proof = proof.expect("k < i+1 and i < n <= capacity cover a full scalar read");
    for bound in &bounds {
        assert!(
            premises.contains(bound),
            "captured full-span proof omitted {bound:?}"
        );
    }
    let captured = premises
        .into_iter()
        .fold(PureFactContext::new(), PureFactContext::assume_proposition);
    let step = CMemoryDerivation::Store {
        base: intern_c_memory(CMemory::new()),
        pointer: write.clone(),
        value: CValue::Int32(7u32.into()),
    };
    assert!(proof.checks(&step, &read, 4, &facts));
    assert!(proof.checks(&step, &read, 4, &captured));
    for bound in &bounds {
        assert!(!proof.checks(&step, &read, 4, &captured.without_exact_fact(bound)));
    }
    assert!(!proof.checks(&step, &read, 8, &facts));
    assert!(
        typed_store_separated_ranges_evidence(
            &write,
            4,
            &read,
            4,
            &facts.without_exact_fact(&lower)
        )
        .is_none()
    );
}

#[test]
fn retained_indexed_access_refuses_a_modularly_equal_wrapped_displacement() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let first_index = Bitvector32Term::Variable(Variable(9_887_200));
    let second_index = Bitvector32Term::Variable(Variable(9_887_202));
    let index = Bitvector32Term::add(first_index.clone(), second_index.clone());
    let read = base.offset_by_elements(index.clone(), 4);
    let write = Pointer::symbolic(Variable(9_887_201));
    let read_range = range(base.clone(), 2, 4);
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(0u32.into(), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index.clone(), 2u32.into()),
            true,
        )
        .assume_proposition(Proposition::CResourceSeparate {
            left: Box::new(CResource::Memory(range(write.clone(), 1, 4))),
            right: Box::new(CResource::Memory(read_range.clone())),
        });
    let proof = typed_store_separated_ranges_evidence(&write, 4, &read, 4, &assumptions)
        .expect("the selected index bounds cover the complete scalar read");
    let step = CMemoryDerivation::Store {
        base: intern_c_memory(CMemory::new()),
        pointer: write.clone(),
        value: CValue::Int32(7u32.into()),
    };
    assert!(proof.checks(&step, &read, 4, &assumptions));
    let wrapped = Pointer {
        block: read.block.clone(),
        // Two signed minima have residue zero, but their exact sum is
        // negative 2^32 elements. Bounds on the residue cannot cover that span.
        offset: PointerOffsetTerm::add(
            PointerOffsetTerm::scale_int32(first_index, 4),
            PointerOffsetTerm::scale_int32(second_index, 4),
        ),
    };
    assert_eq!(
        wrapped.element_index_from_base_with_width(&base, 4),
        Some(index)
    );
    assert!(!proof.checks(&step, &wrapped, 4, &assumptions));
    assert!(typed_store_separated_ranges_evidence(&write, 4, &wrapped, 4, &assumptions).is_none());
}

#[test]
fn after_end_access_captures_only_its_retained_order_premises() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer::symbolic(Variable(9_887_300));
    let start = Bitvector32Term::Variable(Variable(9_887_301));
    let end = Bitvector32Term::Variable(Variable(9_887_302));
    let index = Bitvector32Term::Variable(Variable(9_887_303));
    let selected = CMemoryRange::new(base.clone(), start.clone(), end.clone());
    let pointer = base.offset_by_elements(index.clone(), 4);
    let bounds = [
        Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(0u32.into(), start.clone()),
            true,
        ),
        Proposition::ConditionIs(ConditionTerm::signed_less_equal(start, end.clone()), true),
        Proposition::ConditionIs(ConditionTerm::signed_less_equal(end, index), true),
    ];
    let facts = bounds
        .iter()
        .cloned()
        .fold(PureFactContext::new(), PureFactContext::assume_proposition);
    let (proof, premises) = crate::kernel::collect_reasoning_provenance(|| {
        crate::kernel::capture_implicit_reasoning_provenance(|| {
            RangeDisjointFromPointerEvidence::for_after_end(&selected, &pointer, 8, &facts)
        })
    });
    let proof = proof.expect("a complete forward access starts after the ordered range");
    assert_eq!(premises.len(), bounds.len());
    let captured = premises
        .into_iter()
        .fold(PureFactContext::new(), PureFactContext::assume_proposition);
    assert!(proof.checks(&selected, &pointer, 8, &captured));
    for bound in &bounds {
        assert!(!proof.checks(&selected, &pointer, 8, &captured.without_exact_fact(bound)));
    }
}

#[test]
fn symbolic_loop_footprint_frames_a_complete_separated_read_with_captured_bounds() {
    let _session = crate::kernel::VerificationSession::enter();
    let length = Bitvector32Term::Variable(Variable(9_887_400));
    let dst_capacity = Bitvector32Term::Variable(Variable(9_887_401));
    let src_capacity = Bitvector32Term::Variable(Variable(9_887_402));
    let index = Bitvector32Term::Variable(Variable(9_887_403));
    let dst = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(9_887_404)), 4),
    };
    let src = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(9_887_405)), 4),
    };
    let footprint = CMemoryRange::new(dst.clone(), 0u32.into(), length.clone());
    let separation = Proposition::CResourceSeparate {
        left: Box::new(CResource::Memory(CMemoryRange::new(
            dst,
            0u32.into(),
            dst_capacity.clone(),
        ))),
        right: Box::new(CResource::Memory(CMemoryRange::new(
            src.clone(),
            0u32.into(),
            src_capacity.clone(),
        ))),
    };
    let length_lower = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(0u32.into(), length.clone()),
        true,
    );
    let length_upper = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(length.clone(), dst_capacity.clone()),
        true,
    );
    let dst_fits = Proposition::ConditionIs(
        ConditionTerm::unsigned_less_equal(dst_capacity.clone(), 1_073_741_823u32.into()),
        true,
    );
    let src_fits = Proposition::ConditionIs(
        ConditionTerm::unsigned_less_equal(src_capacity.clone(), 1_073_741_823u32.into()),
        true,
    );
    let assumptions = [
        separation.clone(),
        length_lower.clone(),
        length_upper.clone(),
        dst_fits.clone(),
        src_fits,
        Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(length.clone(), src_capacity),
            true,
        ),
        Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(0u32.into(), index.clone()),
            true,
        ),
        Proposition::ConditionIs(ConditionTerm::signed_less_than(index.clone(), length), true),
    ]
    .into_iter()
    .fold(PureFactContext::new(), PureFactContext::assume_proposition);
    let read = src.offset_by_elements(index, 4);
    let (ranges, premises) = crate::kernel::collect_reasoning_provenance(|| {
        crate::kernel::capture_implicit_reasoning_provenance(|| {
            typed_ranges_disjoint_from_pointer_evidence(
                &[footprint.clone()],
                &read,
                4,
                &assumptions,
            )
        })
    });
    let ranges = ranges.expect(
        "length <= capacity places the whole loop write footprint inside its separated owner",
    );
    for required in [&separation, &length_lower, &length_upper, &dst_fits] {
        assert!(
            premises.contains(required),
            "the loop frame omitted a consumed extent premise"
        );
    }
    let captured = premises
        .into_iter()
        .fold(PureFactContext::new(), PureFactContext::assume_proposition);
    let step = CMemoryDerivation::LoopHavoc {
        base: intern_c_memory(CMemory::new()),
        variable: Variable(9_887_406),
        mutable_ranges: Some(vec![footprint.clone()]),
    };
    let proof = MemoryDagHopJustification::LoopHavocRanges { ranges };
    assert!(proof.checks(&step, &read, 4, &captured));
    assert!(!proof.checks(&step, &read, 8, &captured));
    for required in [&separation, &length_lower, &length_upper, &dst_fits] {
        assert!(!proof.checks(&step, &read, 4, &captured.without_exact_fact(required)));
    }
    let beyond_owner = CMemoryDerivation::LoopHavoc {
        base: intern_c_memory(CMemory::new()),
        variable: Variable(9_887_406),
        mutable_ranges: Some(vec![footprint.with_bounds(
            footprint.base().clone(),
            0u32.into(),
            Bitvector32Term::add(dst_capacity, 1u32.into()),
        )]),
    };
    assert!(!proof.checks(&beyond_owner, &read, 4, &captured));
}
