use super::*;

fn opaque(id: u64) -> OldPointer {
    OldPointer::new(Address::symbolic(Variable(id)), ProgramType::Int32Pointer)
}

/// The witness arrives after the entire related class has been built. Each
/// sample measures the first query after admission, not a warmed query cache.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: cold domain queries across growing alias classes take 2.5s"]
fn pointer_domain_queries_read_cached_classes_without_alias_discovery() {
    for unrelated in [0u64, 32, 128] {
        for related in [4u64, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let root = opaque(998_000);
            let selected = root.clone().with_bounds(Some(SubobjectBounds {
                start: root.address().clone(),
                width: 4u32.into(),
            }));
            let mut facts = PureFactContext::new();
            for i in 0..unrelated {
                facts = facts.assume_condition(
                    OldConditionTerm::pointer_equal(
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
                    OldConditionTerm::pointer_equal(previous, next.clone()),
                    true,
                );
                previous = next;
            }
            facts = facts.assume_condition(
                OldConditionTerm::pointer_equal(previous, selected.clone()),
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
            // Consumers query the same cold class without rewriting the value.
            let ((paths, clause), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    let paths = crate::kernel::eval::pointer_offset_by_bytes_paths(
                        &ExecutionState::new(),
                        first.clone(),
                        4,
                        ExecutionFacts::new(),
                        Vec::new(),
                        &facts,
                    );
                    let range =
                        MemoryRange::from_pointer_value(&first, 0u32.into(), 1u32.into(), 4);
                    let clause =
                        crate::kernel::loops::memory_range_bounds_refusal(&first, &range, &facts);
                    (paths, clause)
                });
            assert!(clause.is_none());
            assert_eq!(paths.len(), 1);
            assert_eq!(
                paths[0].outcome,
                ExpressionOutcome::Value(ProgramValue::Pointer(
                    first
                        .clone()
                        .with_address(first.address().offset_by_bytes(4))
                ))
            );
            assert!(
                work <= 512 * logarithm + 1024,
                "related={related}, unrelated={unrelated}, consumer work={work}"
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
        let mut memory = SymbolicMemory::new();
        for i in 0..stores {
            memory = memory.store(
                Address::symbolic(Variable(1_000_000 + i)),
                ProgramValue::Int32(7u32.into()),
            );
        }
        let memory = crate::kernel::intern_memory(memory);
        let cell = Address::symbolic(Variable(1_001_000));
        let read = OldPointer::from_read(
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

fn coverage(value: &OldPointer, start: u32, end: u32) -> Proposition {
    value
        .opaque_coverage_fact(&MemoryRange::from_pointer_value(
            value,
            start.into(),
            end.into(),
            1,
        ))
        .unwrap()
}

/// A broader holding supplies an opaque pointer's access once coverage
/// evidence for that pointer's own domain contains the accessed bytes. The
/// query reads only the coverage bucket of the required domain: unrelated
/// coverage leaves its cost flat, and related coverage of the same domain
/// costs at most linearly.
#[test]
fn a_broader_holding_supplies_bytes_its_reader_has_coverage_for() {
    let mut unrelated_samples = Vec::new();
    for unrelated in [0u32, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let p = opaque(1_002_000);
        let held = MemoryRange::from_pointer_value(
            &p.clone().with_root_bounds(),
            0u32.into(),
            4u32.into(),
            1,
        );
        let required = p.access_provenance();
        let mut facts = PureFactContext::new();
        for i in 0..unrelated {
            let other = opaque(1_003_000 + u64::from(i));
            facts = facts.assume_proposition(coverage(&other, 0, 4));
        }
        // No evidence for `p`'s own domain: the broader holding refuses.
        assert!(!facts.access_provenance_matches_bytes(required, p.address(), 1, &held));
        let facts = facts.assume_proposition(coverage(&p, 0, 2));
        let (inside, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.access_provenance_matches_bytes(required, p.address(), 1, &held)
        });
        assert!(inside);
        // Bytes past the coverage stay refused, though the holding has them.
        let beyond = p.address().offset_by_bytes(2);
        assert!(!facts.access_provenance_matches_bytes(required, &beyond, 1, &held));
        // Another object's holding at no proven provenance supplies nothing.
        let other = opaque(1_004_000);
        let elsewhere =
            MemoryRange::from_pointer_value(&other.with_root_bounds(), 0u32.into(), 4u32.into(), 1);
        assert!(!facts.access_provenance_matches_bytes(required, p.address(), 1, &elsewhere));
        unrelated_samples.push(work);
    }
    assert!(
        unrelated_samples
            .iter()
            .all(|work| *work <= unrelated_samples[0] + 8),
        "unrelated coverage changed the query: {unrelated_samples:?}"
    );

    let mut related_samples = Vec::new();
    for related in [1u32, 8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let p = opaque(1_005_000);
        let held = MemoryRange::from_pointer_value(
            &p.clone().with_root_bounds(),
            0u32.into(),
            4u32.into(),
            1,
        );
        let mut facts = PureFactContext::new();
        // Coverage of the same domain that does not reach the accessed byte.
        for i in 0..related {
            facts = facts.assume_proposition(coverage(&p, 8 + i, 9 + i));
        }
        let facts = facts.assume_proposition(coverage(&p, 0, 2));
        let (inside, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.access_provenance_matches_bytes(p.access_provenance(), p.address(), 1, &held)
        });
        assert!(inside);
        related_samples.push((related, work));
    }
    let (base, base_work) = related_samples[0];
    for (related, work) in &related_samples {
        assert!(
            *work <= base_work + 32 * (related - base) as usize,
            "related coverage grew the query superlinearly: {related_samples:?}"
        );
    }
}
