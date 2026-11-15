use super::*;

#[test]
fn mixed_return_composition_ignores_related_aliases_and_retained_owners() {
    for axis in ["aliases", "related owners", "unrelated owners"] {
        let mut samples = Vec::new();
        for count in [4_u32, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let pointer = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(8_820_000)),
            };
            let other = |id: u32| Pointer::symbolic(Variable(8_830_000 + u64::from(id)));
            let owner = |base, start: u32| {
                ResourceFact::own_memory(MemoryRange::new(base, start.into(), (start + 1).into()))
            };
            let mut facts = PureFactContext::new();
            let mut frame = ResourceContext::new_with_equalities(&facts)
                .unchecked_with_fact(owner(pointer.clone(), 4));
            for index in 0..count {
                match axis {
                    "aliases" => {
                        facts = facts.assume_condition(
                            ConditionTerm::pointer_equal(pointer.clone(), other(index)),
                            true,
                        )
                    }
                    "related owners" => {
                        frame = frame.unchecked_with_fact(owner(pointer.clone(), index * 4 + 8))
                    }
                    _ => frame = frame.unchecked_with_fact(owner(other(index), 0)),
                }
            }
            frame.synchronize_memory_equalities(&facts);
            let borrowed = owner(pointer, 0);
            let produced = owner(other(1_000), 0);
            let evaluated = EvaluatedReturnResources {
                resources: ResourceContext::new_with_equalities(&facts)
                    .unchecked_with_facts([produced.clone(), borrowed.clone()]),
                entry_borrows: vec![false, true],
            };
            let ((result, occurrences), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    let _operation = crate::kernel::search::FastOperationScope::enter(
                        "mixed borrowed/produced return",
                    );
                    evaluated
                        .restore_entry_borrows(
                            frame.clone(),
                            ReturnResourceComposition::RestoreEntryBorrows,
                            &facts,
                        )
                        .unwrap()
                        .finish(&facts)
                        .unwrap()
                });
            assert_eq!(result.facts().len(), frame.facts().len() + 2);
            assert_eq!(occurrences[0].0, produced);
            assert_eq!(occurrences[1].0, borrowed);
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 48),
            "{axis}: {samples:?}"
        );
    }
}
