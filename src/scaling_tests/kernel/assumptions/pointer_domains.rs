use super::*;

fn opaque(id: u64) -> PointerValue {
    PointerValue::new(Address::symbolic(Variable(id)), ProgramType::Int32Pointer)
}

/// The witness arrives after the entire related class has been built. Each
/// sample measures the first query after admission, not a warmed query cache.
#[test]
#[ignore = "nightly: cold domain queries across growing alias classes take 2.5s"]
fn pointer_domain_queries_read_cached_classes_without_alias_discovery() {
    for unrelated in [0u64, 32, 128] {
        for related in [4u64, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let root = opaque(998_000);
            let selected = root.clone().with_bounds(Some(SubobjectBounds {
                start: root.pointer().clone(),
                width: 4u32.into(),
            }));
            let mut facts = PureFactContext::new();
            for i in 0..unrelated {
                facts = facts.assume_condition(
                    ConditionTerm::pointer_value_equal(
                        opaque(998_100 + 2 * i),
                        opaque(998_101 + 2 * i),
                    ),
                    true,
                );
            }
            let first = opaque(999_000);
            let mut previous = first.clone();
            for i in 1..related {
                let next = opaque(999_000 + i);
                facts = facts.assume_condition(
                    ConditionTerm::pointer_value_equal(previous, next.clone()),
                    true,
                );
                previous = next;
            }
            facts = facts.assume_condition(
                ConditionTerm::pointer_value_equal(previous, selected.clone()),
                true,
            );
            let ((domain, work), map_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| facts.pointer_domain(&first))
            });
            assert_eq!(
                domain,
                PointerDomain::Selected(selected.bounds().unwrap().clone())
            );
            let logarithm = (related + unrelated + 1).ilog2() as usize + 1;
            assert!(
                work <= 16 * logarithm + 32,
                "related={related}, unrelated={unrelated}, work={work}"
            );
            assert!(
                map_work <= 128 * logarithm + 128,
                "related={related}, unrelated={unrelated}, map work={map_work}"
            );
            let held = MemoryRange::from_pointer_value(&selected, 0u32.into(), 1u32.into(), 4);
            let (matched, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.access_provenance_match(first.access_provenance(), &held)
            });
            assert!(matched);
            assert!(
                work <= 128 * logarithm + 512,
                "related={related}, unrelated={unrelated}, access work={work}"
            );
        }
    }
}

#[test]
fn an_unregistered_pointer_domain_does_not_recover_memory_history() {
    for stores in [0u64, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut memory = Memory::new();
        for i in 0..stores {
            memory = memory.store(
                Address::symbolic(Variable(1_000_000 + i)),
                ProgramValue::Int32(7u32.into()),
            );
        }
        let memory = crate::kernel::intern_memory(memory);
        let cell = Address::symbolic(Variable(1_001_000));
        let read = PointerValue::from_read(
            Address::loaded_value(&memory, &cell),
            ProgramType::Int32Pointer,
            &memory,
            &cell,
        );
        let facts = PureFactContext::new();
        let (domain, work) =
            crate::instrumentation::measure_deterministic_work(|| facts.pointer_domain(&read));
        assert_eq!(domain, PointerDomain::Unknown);
        assert!(work <= 8, "stores={stores}, work={work}");
    }
}
