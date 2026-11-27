#[test]
fn selected_context_does_not_withdraw_ambient_pointer_facts() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let selected =
            Proposition::condition_is(OldConditionTerm::Variable(Variable(700_000)), true);
        let mut context = PureFactContext::new().assume_proposition(selected.clone());
        for index in 0..size {
            context = context.assume_proposition(Proposition::Predicate {
                name: "pointer_fact".into(),
                arguments: vec![Term::ProgramValue(
                    (ProgramValue::Pointer(Pointer::new(
                        Address::new(
                            format!("ambient_{index}").into(),
                            AddressOffset::constant(0),
                        ),
                        ProgramType::Int32Pointer,
                    )))
                    .into(),
                )],
            });
        }
        let (restricted, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.restricted_to_facts(
                &[(OldConditionTerm::Variable(Variable(700_000)), true)],
                &[],
            )
        });
        assert!(restricted.contains_assumed_exact(&selected));
        assert_eq!(restricted.fact_counts(), (1, 0));
        assert_eq!(context.fact_counts(), (1, size as usize));
        samples.push(work);
    }
    eprintln!("restriction work: {samples:?}");
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 16),
        "ambient withdrawal: {samples:?}"
    );
}

#[test]
fn memory_view_miss_does_not_scan_other_bases_in_one_block() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = SymbolicMemory::new();
        let pointer = |id| {
            Address::new(
                AddressBase::ExternalArgument,
                AddressOffset::scale_int32(OldMachineTerm::Variable(Variable(id)), 4),
            )
        };
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_proposition(Proposition::MemoryLoadable {
                point: Default::default(),
                memory: memory.clone(),
                base: pointer(720_000 + index),
                bytes: (OldMachineTerm::constant(4)).into(),
                wide: false,
            });
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert!(!context.proves_memory_loadable(
                    &memory,
                    &Default::default(),
                    &pointer(730_000),
                    &OldMachineTerm::constant(4)
                ));
            }
        });
        samples.push(work);
    }
    eprintln!("view miss work: {samples:?}");
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 16),
        "shared block scan: {samples:?}"
    );
}

#[test]
fn atom_memory_condition_miss_does_not_scan_open_fact_family() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let term = |id| OldMachineTerm::Variable(Variable(id));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(
                OldConditionTerm::signed_less_than(
                    OldMachineTerm::add(term(740_000 + index * 2), OldMachineTerm::constant(1)),
                    term(740_001 + index * 2),
                ),
                true,
            );
        }
        let query = OldConditionTerm::signed_less_than(term(750_000), term(750_001));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert!(!context.has_matching_condition_fact_for_memory_resolution(&query, true));
            }
        });
        samples.push(work);
    }
    eprintln!("atom memory miss work: {samples:?}");
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 16),
        "open family scan: {samples:?}"
    );
}

#[test]
fn adjacent_view_looks_up_its_suffix_beside_unrelated_cells_and_ranges() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Address::new("adjacent".into(), AddressOffset::constant(0));
        let prefix = Proposition::MemoryLoadable {
            point: Default::default(),
            memory: SymbolicMemory::new(),
            base: base.clone(),
            bytes: 8.into(),
            wide: false,
        };
        let suffix = Proposition::MemoryLoadable {
            point: Default::default(),
            memory: SymbolicMemory::new(),
            base: base.offset_by_bytes(8),
            bytes: 4.into(),
            wide: false,
        };
        let mut context = PureFactContext::new()
            .assume_proposition(prefix.clone())
            .assume_proposition(suffix.clone());
        let mut memory = SymbolicMemory::new();
        for index in 0..size {
            let other = base.offset_by_bytes(1000 + index as u32 * 4);
            context = context.assume_proposition(Proposition::MemoryLoadable {
                point: Default::default(),
                memory: SymbolicMemory::new(),
                base: other.clone(),
                bytes: 4.into(),
                wide: false,
            });
            memory = memory.store(other, ProgramValue::Int32(7.into()));
        }
        let (facts, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.adjacent_loadable_region_facts(
                &SymbolicMemory::new(),
                &Default::default(),
                &base,
                &12.into(),
            )
        });
        assert_eq!(facts.unwrap(), vec![prefix.clone(), suffix]);
        let selected = PureFactContext::new().assume_proposition(prefix.clone());
        let memory = memory.store(base.offset_by_bytes(8), ProgramValue::Int32(9.into()));
        let (facts, stored_work) = crate::instrumentation::measure_deterministic_work(|| {
            selected.adjacent_loadable_region_facts(&memory, &Default::default(), &base, &12.into())
        });
        assert_eq!(facts.unwrap(), vec![prefix]);
        assert!(
            selected
                .adjacent_loadable_region_facts(&memory, &Default::default(), &base, &16.into())
                .is_none()
        );
        samples.push(work + stored_work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 16),
        "adjacent view work: {samples:?}"
    );
}

#[test]
fn exact_view_candidate_does_not_prepare_its_alias_class() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Address::symbolic(Variable(770_000));
        let fact = Proposition::MemoryLoadable {
            point: Default::default(),
            memory: SymbolicMemory::new(),
            base: base.clone(),
            bytes: 8.into(),
            wide: false,
        };
        let mut context = PureFactContext::new().assume_proposition(fact.clone());
        for index in 0..size {
            context
                .equality_graph
                .add_equality(&base, &Address::symbolic(Variable(770_001 + index)));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert_eq!(
                    context.memory_loadable_candidates_for_base(&base).next(),
                    Some(&fact)
                );
            }
        });
        samples.push(work);
    }
    eprintln!("exact view candidate work: {samples:?}");
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "eager alias preparation: {samples:?}"
    );
}

#[test]
fn memory_view_miss_does_not_scan_same_address_spans() {
    let mut samples = Vec::new();
    for size in [8u32, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = SymbolicMemory::new();
        let base = Address::symbolic(Variable(780_000));
        let mut context = PureFactContext::new();
        for span in 1..=size {
            context = context.assume_proposition(Proposition::MemoryLoadable {
                point: Default::default(),
                memory: memory.clone(),
                base: base.clone(),
                bytes: span.into(),
                wide: false,
            });
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert!(!context.proves_memory_loadable(
                    &memory,
                    &Default::default(),
                    &base,
                    &4096.into()
                ));
            }
        });
        assert!(context.proves_memory_loadable(&memory, &Default::default(), &base, &size.into()));
        samples.push(work);
    }
    eprintln!("same address view miss work: {samples:?}");
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 16),
        "same address bucket scan: {samples:?}"
    );
}

#[test]
fn ambiguous_view_buckets_keep_exact_and_selected_evidence() {
    for wide in [false, true] {
        for retained_states in [false, true] {
            let mut misses = Vec::new();
            let mut hits = Vec::new();
            let mut selected_work = Vec::new();
            for size in [8u32, 32, 128] {
                let _session = crate::kernel::VerificationSession::enter();
                let memory = SymbolicMemory::new();
                let base = Address::symbolic(Variable(790_000));
                let span = |n: u32| {
                    if wide {
                        OldMachineTerm::uint64_constant(u64::from(n))
                    } else {
                        OldMachineTerm::constant(n)
                    }
                };
                let mut context = PureFactContext::new();
                let mut selected = None;
                for index in 1..=size {
                    let source = if retained_states {
                        memory.clone().store(
                            Address::symbolic(Variable(790_001 + u64::from(index))),
                            ProgramValue::Int32(7.into()),
                        )
                    } else {
                        memory.clone()
                    };
                    let fact = Proposition::MemoryLoadable {
                        point: Default::default(),
                        memory: source,
                        base: base.clone(),
                        bytes: crate::kernel::StoredMachineTerm::new(
                            if wide {
                                crate::kernel::MachineIntegerType::UInt64
                            } else {
                                crate::kernel::MachineIntegerType::Int32
                            },
                            span(index * 4),
                        ),
                        wide,
                    };
                    if index == size / 2 {
                        selected = Some(fact.clone());
                    }
                    context = context.assume_proposition(fact);
                }
                let selected = selected.unwrap();
                let proves = |context: &PureFactContext, bytes: &OldMachineTerm| {
                    if wide {
                        context.proves_native_memory_loadable(
                            &memory,
                            &Default::default(),
                            &base,
                            bytes,
                        )
                    } else {
                        context.proves_memory_loadable(&memory, &Default::default(), &base, bytes)
                    }
                };
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    for _ in 0..4 {
                        assert!(!proves(&context, &span(4096)));
                    }
                });
                misses.push(work);
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    for _ in 0..4 {
                        let Proposition::MemoryLoadable { memory, bytes, .. } = &selected else {
                            unreachable!()
                        };
                        assert!(if wide {
                            context.proves_native_memory_loadable(
                                memory,
                                &Default::default(),
                                &base,
                                bytes.old_form(),
                            )
                        } else {
                            context.proves_memory_loadable(
                                memory,
                                &Default::default(),
                                &base,
                                bytes.old_form(),
                            )
                        });
                    }
                });
                assert!(work >= 4, "exact view lookups must charge work");
                hits.push(work);
                // Six bytes is a valid subrange, but no asserted span is six.
                // Ambiguity is a refusal, not an arbitrary premise choice.
                assert!(!proves(&context, &span(6)));
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    let selected_context = crate::kernel::SelectedFacts::from_propositions(
                        std::slice::from_ref(&selected),
                    );
                    assert!(proves(&selected_context, &span(6)));
                    assert!(!proves(&selected_context, &span(4096)));
                });
                selected_work.push(work);
                assert!(!proves(&PureFactContext::new(), &span(6)));
            }
            eprintln!(
                "view buckets wide={wide} states={retained_states}: misses={misses:?}, hits={hits:?}, selected={selected_work:?}"
            );
            for samples in [misses, hits, selected_work] {
                assert!(
                    samples.iter().all(|work| *work <= samples[0] + 16),
                    "{samples:?}"
                );
            }
        }
    }
}

#[test]
fn atomic_view_miss_cannot_reopen_coverage_bucket_scans() {
    for same_address in [false, true] {
        let mut samples = Vec::new();
        for size in [8u32, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let memory = SymbolicMemory::new();
            let base = Address::symbolic(Variable(796_000));
            let mut context = PureFactContext::new();
            for index in 1..=size {
                context = context.assume_proposition(Proposition::MemoryLoadable {
                    point: Default::default(),
                    memory: memory.clone(),
                    base: if same_address {
                        base.clone()
                    } else {
                        base.offset_by_bytes(index * 16)
                    },
                    bytes: index.into(),
                    wide: false,
                });
            }
            let goal = Proposition::MemoryLoadable {
                point: Default::default(),
                memory: memory.clone(),
                base: base.clone(),
                bytes: 4096.into(),
                wide: false,
            };
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..4 {
                    assert!(!context.proves_atomic_without_search(&goal));
                    assert!(!crate::kernel::api::loadable_covered_by_fact(
                        &context, &goal
                    ));
                }
            });
            samples.push(work);
        }
        eprintln!("atomic view miss same_address={same_address}: {samples:?}");
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 16),
            "{samples:?}"
        );
    }
}

#[test]
fn numeric_comparison_view_queries_do_not_scan_supports() {
    use crate::kernel::{IntegerTerm as I, SharedIntegerTerm};
    let mut samples = Vec::new();
    for size in [8i64, 32, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut context = PureFactContext::new();
        let view = Proposition::Or(
            Box::new(Proposition::condition_is(
                OldConditionTerm::equal(
                    OldMachineTerm::Variable(Variable(880000)),
                    OldMachineTerm::constant(i32::MIN as u32),
                ),
                false,
            )),
            Box::new(Proposition::condition_is(
                OldConditionTerm::Variable(Variable(880001)),
                true,
            )),
        );
        for index in 0..size {
            let bound: SharedIntegerTerm = I::Subtract(
                I::constant_i64(index).into(),
                I::constant_i64(index + 2147483648).into(),
            )
            .into();
            let source = Proposition::Or(
                Box::new(Proposition::condition_is(
                    OldConditionTerm::IntegerNotEqual(
                        I::from_machine(
                            MachineIntegerType::Int32,
                            OldMachineTerm::Variable(Variable(880000)),
                        )
                        .unwrap()
                        .into(),
                        bound,
                    ),
                    true,
                )),
                Box::new(Proposition::condition_is(
                    OldConditionTerm::Variable(Variable(880001)),
                    true,
                )),
            );
            context.insert_proposition_fact(source);
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(context.contains_proposition_fact(&view));
        });
        samples.push(work);
        context.clear_proposition_facts();
        assert!(!context.contains_proposition_fact(&view));
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "{samples:?}"
    );
}
