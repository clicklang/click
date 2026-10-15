// Scaling tests of `src/kernel/resource_tracker/cell_source.rs` (module `borrowed_range_frame_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn borrowed_range_frame_is_indexed_full_width_and_authority_scoped() {
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer::symbolic(Variable(9_897_001));
        let data = Pointer::symbolic(Variable(9_897_002));
        let count = Bitvector32Term::Variable(Variable(9_897_003));
        let backing = CMemoryRange::new_with_element_width(data, 0u32.into(), count.clone(), 4);
        let descriptor =
            CMemoryRange::new_with_element_width(field.clone(), 0u32.into(), 2u32.into(), 4);
        let mut partition = ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own_memory(backing.clone()))
            .unchecked_with_fact(CResourceFact::view_memory(descriptor.clone()));
        for index in 0..size {
            partition = partition.unchecked_with_fact(CResourceFact::own_memory(
                CMemoryRange::new_with_element_width(
                    Pointer::symbolic(Variable(9_898_000 + index)),
                    0u32.into(),
                    4u32.into(),
                    4,
                ),
            ));
        }
        let bare = partition.clone();
        let view = CResourceFact::view_memory(descriptor.clone());
        let support = partition.occurrences_for_fact(&view)[0];
        let ledger = LoanLedger::new();
        let holder = ledger.fresh_participant().unwrap();
        let opening = ledger
            .borrowed_contract_input(holder, support, view.clone(), None)
            .unwrap();
        let ledger = ledger.apply(&opening.transition).unwrap();
        assert!(ledger.permits_view(
            holder,
            &opening.description,
            opening.root_share,
            &PureFactContext::new()
        ));
        let partition = partition.with_loan_dependency(
            support,
            LoanViewBinding {
                loan: opening.loan,
                scope: opening.scope,
                share: opening.root_share,
                support,
                viewed: view,
                hold: None,
            },
        );
        let bound = partition.clone();
        let authority = Proposition::CResourceComposition(partition);
        let context = PureFactContext::new()
            .assume_proposition(authority.clone())
            .assume_condition(
                ConditionTerm::signed_less_equal(0u32.into(), count.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(count.clone(), 536870911u32.into()),
                true,
            );
        let bare =
            PureFactContext::new().assume_proposition(Proposition::CResourceComposition(bare));
        assert!(typed_range_disjoint_from_pointer_evidence(&backing, &field, 8, &bare).is_none());
        let (proof, work) = crate::instrumentation::measure_deterministic_work(|| {
            typed_range_disjoint_from_pointer_evidence(&backing, &field, 8, &context)
        });
        let proof = proof.expect("held view is separate from the backing owner");
        eprintln!("borrowed range frame: owners={size}, work={work}");
        assert!(work < 200, "size={size}, work={work}");
        assert!(proof.checks(&backing, &field, 8, &context));
        assert!(!proof.checks(&backing, &field, 12, &context));
        let wider_range = CMemoryRange::new_with_element_width(
            backing.base().clone(),
            0u32.into(),
            Bitvector32Term::add(count.clone(), 1u32.into()),
            4,
        );
        assert!(!proof.checks(&wider_range, &field, 8, &context));
        assert!(
            typed_range_disjoint_from_pointer_evidence(&wider_range, &field, 8, &context).is_none()
        );
        let overlapping = context.clone().assume_condition(
            ConditionTerm::pointer_equal(backing.base().clone(), field.clone()),
            true,
        );
        assert!(!proof.checks(&backing, &field, 8, &overlapping));
        assert!(
            typed_range_disjoint_from_pointer_evidence(&backing, &field, 8, &overlapping).is_none()
        );
        // Exercise the complete explicit equality certificate, including
        // the actual LoopHavoc edge and all eight descriptor-read bytes.
        let before = CMemory::new();
        let after = before.clone().with_loop_memory_havoc_preserving_loans(
            Variable(9_897_004),
            &std::collections::BTreeSet::new(),
            Some(std::slice::from_ref(&backing)),
            None,
        );
        let load = |memory: &CMemory| {
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory_ref(memory),
                Box::new(field.clone()),
                LoadKind::Bits64,
            )
        };
        assert!(
            crate::kernel::explicit_atomic_equality_from_memory_derivations(
                &load(&before),
                &load(&after),
                &context,
            )
        );
        // Keep the candidate index while withdrawing its retained authority.
        let mut withdrawn = context.clone();
        withdrawn.resource_compositions = withdrawn.resource_compositions.without_value(&bound);
        assert!(!proof.checks(&backing, &field, 8, &withdrawn));
        assert!(
            typed_range_disjoint_from_pointer_evidence(&backing, &field, 8, &withdrawn).is_none()
        );
        assert!(
            typed_range_disjoint_from_pointer_evidence(&backing, &field, 12, &context).is_none()
        );
        assert!(
            typed_range_disjoint_from_pointer_evidence(&descriptor, &field, 8, &context).is_none()
        );
        let views = ResourceContext::new()
            .unchecked_with_fact(CResourceFact::view_memory(backing.clone()))
            .unchecked_with_fact(CResourceFact::view_memory(descriptor));
        let views =
            PureFactContext::new().assume_proposition(Proposition::CResourceComposition(views));
        assert!(typed_range_disjoint_from_pointer_evidence(&backing, &field, 8, &views).is_none());
    }
}
