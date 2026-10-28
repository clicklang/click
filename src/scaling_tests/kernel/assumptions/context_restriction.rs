#[test]
fn selected_context_does_not_withdraw_ambient_pointer_facts() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let selected = Proposition::ConditionIs(ConditionTerm::Variable(Variable(700_000)), true);
        let mut context = PureFactContext::new().assume_proposition(selected.clone());
        for index in 0..size {
            context = context.assume_proposition(Proposition::Predicate {
                name: "pointer_fact".into(),
                arguments: vec![Term::CValue(CValue::Pointer(CPointerValue::new(
                    Pointer { block: format!("ambient_{index}").into(), offset: PointerOffsetTerm::Constant(0) },
                    CType::Int32Pointer,
                )))],
            });
        }
        let (restricted, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.restricted_to_facts(&[(ConditionTerm::Variable(Variable(700_000)), true)], &[])
        });
        assert!(restricted.contains_assumed_exact(&selected));
        assert_eq!(restricted.fact_counts(), (1, 0));
        assert_eq!(context.fact_counts(), (1, size as usize));
        samples.push(work);
    }
    eprintln!("restriction work: {samples:?}");
    assert!(samples.iter().all(|work| *work <= samples[0] + 16), "ambient withdrawal: {samples:?}");
}

#[test]
fn memory_view_miss_does_not_scan_other_bases_in_one_block() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = CMemory::new();
        let pointer = |id| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(id)), 4),
        };
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_proposition(Proposition::CMemoryLoadable {
                memory: memory.clone(), base: pointer(720_000 + index),
                bytes: Bitvector32Term::Constant(4), wide: false,
            });
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert!(!context.proves_memory_loadable(&memory, &pointer(730_000), &Bitvector32Term::Constant(4)));
            }
        });
        samples.push(work);
    }
    eprintln!("view miss work: {samples:?}");
    assert!(samples.iter().all(|work| *work <= samples[0] + 16), "shared block scan: {samples:?}");
}

#[test]
fn atom_memory_condition_miss_does_not_scan_open_fact_family() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let term = |id| Bitvector32Term::Variable(Variable(id));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(ConditionTerm::signed_less_than(
                Bitvector32Term::add(term(740_000 + index * 2), Bitvector32Term::Constant(1)),
                term(740_001 + index * 2)), true);
        }
        let query = ConditionTerm::signed_less_than(term(750_000), term(750_001));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert!(!context.has_matching_condition_fact_for_memory_resolution(&query, true));
            }
        });
        samples.push(work);
    }
    eprintln!("atom memory miss work: {samples:?}");
    assert!(samples.iter().all(|work| *work <= samples[0] + 16), "open family scan: {samples:?}");
}

#[test]
fn adjacent_view_looks_up_its_suffix_beside_unrelated_cells_and_ranges() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer { block: "adjacent".into(), offset: PointerOffsetTerm::Constant(0) };
        let prefix = Proposition::CMemoryLoadable { memory: CMemory::new(), base: base.clone(), bytes: 8.into(), wide: false };
        let suffix = Proposition::CMemoryLoadable { memory: CMemory::new(), base: base.offset_by_bytes(8), bytes: 4.into(), wide: false };
        let mut context = PureFactContext::new().assume_proposition(prefix.clone()).assume_proposition(suffix.clone());
        let mut memory = CMemory::new();
        for index in 0..size {
            let other = base.offset_by_bytes(1000 + index as u32 * 4);
            context = context.assume_proposition(Proposition::CMemoryLoadable { memory: CMemory::new(), base: other.clone(), bytes: 4.into(), wide: false });
            memory = memory.store(other, CValue::Int32(7.into()));
        }
        let (facts, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.adjacent_loadable_region_facts(&CMemory::new(), &base, &12.into())
        });
        assert_eq!(facts.unwrap(), vec![prefix.clone(), suffix]);
        let selected = PureFactContext::new().assume_proposition(prefix.clone());
        let memory = memory.store(base.offset_by_bytes(8), CValue::Int32(9.into()));
        let (facts, stored_work) = crate::instrumentation::measure_deterministic_work(|| {
            selected.adjacent_loadable_region_facts(&memory, &base, &12.into())
        });
        assert_eq!(facts.unwrap(), vec![prefix]);
        assert!(selected.adjacent_loadable_region_facts(&memory, &base, &16.into()).is_none());
        samples.push(work + stored_work);
    }
    assert!(samples.iter().all(|work| *work <= samples[0] + 16), "adjacent view work: {samples:?}");
}

#[test]
fn exact_view_candidate_does_not_prepare_its_alias_class() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer::symbolic(Variable(770_000));
        let fact = Proposition::CMemoryLoadable { memory: CMemory::new(), base: base.clone(), bytes: 8.into(), wide: false };
        let mut context = PureFactContext::new().assume_proposition(fact.clone());
        for index in 0..size {
            context.equality_graph.add_equality(&base, &Pointer::symbolic(Variable(770_001 + index)));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert_eq!(context.memory_loadable_candidates_for_base(&base).next(), Some(&fact));
            }
        });
        samples.push(work);
    }
    eprintln!("exact view candidate work: {samples:?}");
    assert!(samples.iter().all(|work| *work == samples[0]), "eager alias preparation: {samples:?}");
}
