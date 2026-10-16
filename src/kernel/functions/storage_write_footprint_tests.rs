use super::*;

#[test]
fn write_extent_must_fit_inside_owned_byte_footprint() {
    let base = Pointer {
        block: "global:owned".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let owned = CMemoryRange::new_with_element_width(
        base.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(4),
        1,
    );
    let assumptions = PureFactContext::new();

    assert!(storage_write_within_owned_footprint(
        &base.offset_by_bytes(2),
        2,
        std::slice::from_ref(&owned),
        &assumptions,
    ));
    assert!(
        !storage_write_within_owned_footprint(
            &base.offset_by_bytes(3),
            2,
            std::slice::from_ref(&owned),
            &assumptions,
        ),
        "the write starts in the footprint but its second byte is outside"
    );
}

/// A write at a symbolic element index is placed in an owned range from
/// the facts bounding the index, exactly at each edge: with a constant
/// displacement, across several elements, and against a symbolic end.
#[test]
fn a_symbolic_index_write_is_placed_by_its_element_bounds() {
    let base = Pointer {
        block: "global:owned".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let j = Bitvector32Term::Variable(Variable(99_001));
    let n = Bitvector32Term::Variable(Variable(99_002));
    let owned = |end: Bitvector32Term| {
        vec![CMemoryRange::new_with_element_width(
            base.clone(),
            Bitvector32Term::Constant(0),
            end,
            4,
        )]
    };
    let bounded = |upper: i32| {
        PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), j.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(j.clone(), Bitvector32Term::Constant(upper as u32)),
                true,
            )
    };
    let at_j = base.offset_by_elements(j.clone(), 4);
    let within =
        |pointer: &Pointer, bytes: u32, owned: &[CMemoryRange], facts: &PureFactContext| {
            storage_write_within_owned_footprint(pointer, bytes, owned, facts)
        };
    let thousand = owned(Bitvector32Term::Constant(1000));
    assert!(within(&at_j, 4, &thousand, &bounded(1000)));
    assert!(!within(&at_j, 4, &thousand, &bounded(1001)));
    // Two elements from `j`: the last is `j + 1`.
    assert!(within(&at_j, 8, &thousand, &bounded(999)));
    assert!(!within(&at_j, 8, &thousand, &bounded(1000)));
    // Two elements past `j`: `j + 2 < 1000`.
    let past = at_j.offset_by_bytes(8);
    assert!(within(&past, 4, &thousand, &bounded(998)));
    assert!(!within(&past, 4, &thousand, &bounded(999)));
    // A byte inside element `j` covers no whole element and is left to
    // the byte comparison, which cannot place a symbolic index.
    assert!(!within(&at_j, 1, &thousand, &bounded(1000)));
    // A symbolic end.
    let up_to_n = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), j.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(j.clone(), n.clone()), true);
    assert!(within(&at_j, 4, &owned(n.clone()), &up_to_n));
    assert!(!within(&at_j, 4, &owned(n.clone()), &bounded(1000)));
    // The lower edge: nothing bounds `j` below.
    let upper_only = PureFactContext::new().assume_condition(
        ConditionTerm::signed_less_than(j.clone(), Bitvector32Term::Constant(10)),
        true,
    );
    assert!(!within(&at_j, 4, &thousand, &upper_only));
}

#[test]
fn memory_effect_write_collection_preserves_each_access_width() {
    let pointer = Pointer {
        block: "global:owned".into(),
        offset: PointerOffsetTerm::Constant(3),
    };
    let fact = ExecutionPureFact::new(Proposition::CMemoryMutatesOnly {
        before: CMemory::new(),
        after: CMemory::new(),
        writes: vec![(pointer.clone(), 1), (pointer.clone(), 2)],
    });

    assert_eq!(
        crate::kernel::reasoning::memory_effect_write_accesses(&[fact]),
        BTreeSet::from([(pointer.clone(), 1), (pointer, 2)]),
    );
}
