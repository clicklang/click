use super::*;

fn memory_range(base: u32, end: u32) -> CMemoryRange {
    CMemoryRange::new(
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        },
        Bitvector32Term::Constant(base),
        Bitvector32Term::Constant(end),
    )
}

#[test]
fn loop_havoc_requires_a_checked_set_disjoint_from_active_loans() {
    let escrow = CResourceFact::own_memory(memory_range(0, 1));
    let support = ResourceContext::new()
        .unchecked_with_fact(escrow.clone())
        .unique_owned_occurrence_for_fact(&escrow)
        .expect("the test escrow has one backing occurrence")
        .0;
    let ledger = super::super::loans::LoanLedger::new();
    let owner = ledger.fresh_participant().unwrap();
    let opening = ledger.lend(owner, owner, support, escrow).unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();

    let assumptions = PureFactContext::new();
    assert!(validate_loop_havoc_stable_loans(&ledger, None, &assumptions).is_err());
    assert!(
        validate_loop_havoc_stable_loans(&ledger, Some(&[memory_range(0, 1)]), &assumptions)
            .is_err()
    );
    assert!(
        validate_loop_havoc_stable_loans(&ledger, Some(&[memory_range(2, 3)]), &assumptions)
            .is_ok()
    );
}

#[test]
fn owned_entry_footprint_names_memory_owners_and_refuses_unnameable_ones() {
    let empty = ResourceContext::new();
    assert_eq!(checked_owned_entry_footprint(&empty), Some(Vec::new()));

    let owned = CResourceFact::own_memory(memory_range(2, 3));
    let viewed = CResourceFact::view_memory(memory_range(0, 1));
    let memory_only = ResourceContext::new()
        .unchecked_with_fact(owned)
        .unchecked_with_fact(viewed);
    // A view lends no write authority, so it is not part of the footprint.
    assert_eq!(
        checked_owned_entry_footprint(&memory_only),
        Some(vec![memory_range(2, 3)])
    );

    // An owned resource whose bytes this level cannot enumerate leaves the
    // write set unknown, so the barrier stays closed rather than shrinking
    // to the memory owners that happen to be nameable.
    let folded = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(memory_range(2, 3)))
        .unchecked_with_fact(CResourceFact::own(CResource::Token {
            name: "tokens".to_string(),
            arguments: Vec::new().into(),
        }));
    assert_eq!(checked_owned_entry_footprint(&folded), None);
}

#[test]
fn restoring_a_loop_frame_retains_complete_pointer_reads_but_not_written_cells() {
    let _session = crate::kernel::VerificationSession::enter();
    let field = CPointerValue::new(Pointer::symbolic(Variable(916_200)), CType::Int32Pointer);
    let data = CPointerValue::new(Pointer::symbolic(Variable(916_201)), CType::Int32Pointer);
    let field_range = CMemoryRange::from_pointer_value(&field, 0u32.into(), 2u32.into(), 4);
    let data_range = CMemoryRange::from_pointer_value(&data, 0u32.into(), 4u32.into(), 4);
    let initial = CMemory::new();
    // Restore scalar cache cells covering one complete pointer.
    let memory = initial
        .materialize_symbolic_cell(field.pointer().clone(), CType::Int32)
        .materialize_symbolic_cell(field.pointer().offset_by_bytes(4), CType::Int32);
    let state = CState::new()
        .with_local("field", CValue::Pointer(field.clone()))
        .with_local("data", CValue::Pointer(data))
        .with_memory(memory)
        .with_resource_context(
            ResourceContext::new()
                .unchecked_with_fact(CResourceFact::own_memory(field_range.clone()))
                .unchecked_with_fact(CResourceFact::own_memory(data_range.clone())),
        );
    let assumptions = PureFactContext::new().assume_proposition(Proposition::CResourceSeparate {
        left: Box::new(
            crate::kernel::region_footprint::byte_resource(&CResource::Memory(field_range))
                .unwrap(),
        ),
        right: Box::new(
            crate::kernel::region_footprint::byte_resource(&CResource::Memory(data_range)).unwrap(),
        ),
    });
    let scalar = |value: u32| CExpression::Value(CValue::Int32(value.into()));
    for (name, length, kept) in [("data", 4, true), ("field", 2, false)] {
        let spec = CResourceSpec::owned_memory(CMemorySegment::new(
            CExpression::Variable(name.into()),
            scalar(0),
            scalar(length),
        ));
        let effect = CLoopEffectCheck::new_with_origin(
            CLoopEffect::Mutable(vec![]),
            CLoopEffectSpan::Whole,
            CLoopEffectOrigin::DeclaredResource,
            None,
        );
        let body = CStatement::Store {
            pointer: CExpression::Variable(name.into()),
            value: scalar(1),
        };
        let head = prepare_loop_top_state(
            &state,
            &[effect],
            &[],
            &[spec],
            &[],
            &body,
            &assumptions,
            &mut ExecutionBudget::default(),
            &mut KernelVariableGenerator::fresh_for_execution(BTreeSet::new()),
        )
        .unwrap();
        assert!(head.resource_failures.is_empty());
        let preservation = crate::kernel::tests::explicit_frame(
            state.memory(),
            head.top.memory(),
            field.pointer(),
            CType::Int32Pointer,
            &head.summaries,
            &assumptions,
        );
        assert_eq!(
            preservation.is_some(),
            kept,
            "only a field outside the loop's explicit write footprint is preserved"
        );
        if let Some((before, after, equality)) = preservation {
            let (CValue::Pointer(before), CValue::Pointer(after)) = (before, after) else {
                panic!("complete pointer observations");
            };
            assert!(
                assumptions
                    .clone()
                    .assume_proposition(equality)
                    .pointer_designations_match(&before, &after)
            );
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/loops/v10_tests.rs");
}
