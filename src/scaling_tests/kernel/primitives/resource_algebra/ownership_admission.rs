use super::*;

#[test]
fn unsupported_admission_never_discovers_related_owners_or_aliases() {
    for aliases in [false, true] {
        let mut samples = Vec::new();
        for count in [4_u32, 16, 64, 256] {
            let pointer = |id| Pointer::symbolic(Variable(8_780_000 + u64::from(id)));
            let mut facts = PureFactContext::new();
            let mut resources = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(
                ResourceFact::own_memory(MemoryRange::new_with_element_width(
                    pointer(0),
                    0u32.into(),
                    4u32.into(),
                    1,
                )),
            );
            for index in 1..count {
                if aliases {
                    facts = facts.assume_condition(
                        ConditionTerm::pointer_equal(pointer(0), pointer(index)),
                        true,
                    );
                } else {
                    resources = resources.unchecked_with_fact(ResourceFact::own_memory(
                        MemoryRange::new_with_element_width(
                            pointer(0),
                            (index * 16).into(),
                            (index * 16 + 4).into(),
                            1,
                        ),
                    ));
                }
            }
            resources.synchronize_memory_equalities(&facts);
            let output = ResourceFact::own_memory(MemoryRange::new_with_element_width(
                pointer(0),
                4u32.into(),
                MachineTerm::Variable(Variable(8_790_000)),
                1,
            ));
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                resources.clone().admit_without_discovery([output], &facts)
            });
            assert!(matches!(result, OwnershipAdmission::Unsupported(_)));
            samples.push(work);
            assert_eq!(
                resources.facts().len(),
                if aliases { 1 } else { count as usize }
            );
        }
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 32),
            "aliases={aliases}: {samples:?}"
        );
    }
}
