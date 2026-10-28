#[test]
fn view_misses_do_not_enumerate_pointer_alias_classes() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer::symbolic(Variable(810_000));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context
                .equality_graph
                .add_equality(&base, &Pointer::symbolic(Variable(810_001 + index)));
        }
        let memory = CMemory::new();
        let goal = Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: 4096.into(),
            wide: false,
        };
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert!(!context.proves_atomic_without_search(&goal));
            }
        });
        samples.push(work);
    }
    eprintln!("alias-class view misses: {samples:?}");
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 16),
        "alias walk: {samples:?}"
    );
}

#[test]
fn selected_view_checks_alias_coordinates_without_enumerating_the_class() {
    for wide in [false, true] {
        let mut hits = Vec::new();
        let mut misses = Vec::new();
        for size in [8u64, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let memory = CMemory::new();
            let root = Pointer::symbolic(Variable(820_000));
            let source = Pointer::symbolic(Variable(820_001));
            let query = Pointer::symbolic(Variable(820_002));
            let extent = |n| {
                if wide {
                    Bitvector32Term::UInt64Constant(n)
                } else {
                    Bitvector32Term::Constant(n as u32)
                }
            };
            let fact = Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: source.clone(),
                bytes: extent(16),
                wide,
            };
            let mut context = PureFactContext::new().assume_proposition(fact);
            context.equality_graph.add_equality(&root, &source);
            context.equality_graph.add_equality(&root, &query);
            for index in 0..size {
                context
                    .equality_graph
                    .add_equality(&root, &Pointer::symbolic(Variable(821_000 + index)));
            }
            let prove = |pointer: &Pointer, bytes| {
                context.proves_atomic_without_search(&Proposition::CMemoryLoadable {
                    memory: memory.clone(),
                    base: pointer.clone(),
                    bytes: extent(bytes),
                    wide,
                })
            };
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..4 {
                    assert!(prove(&query, 8));
                }
            });
            hits.push(work);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..4 {
                    assert!(!prove(&query, 32));
                }
            });
            misses.push(work);
            assert!(!prove(&Pointer::symbolic(Variable(829_000)), 8));
            assert!(!prove(&query.offset_by_bytes(16), 4));
        }
        eprintln!("selected alias view wide={wide}: hits={hits:?}, misses={misses:?}");
        for samples in [hits, misses] {
            assert!(
                samples.iter().all(|work| *work <= samples[0] + 32),
                "{samples:?}"
            );
        }
    }
}

#[test]
fn view_misses_ignore_a_growing_exact_alias_star_in_one_block() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = |id| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(id)),
        };
        let base = pointer(830_000);
        let mut context = PureFactContext::new().assume_proposition(Proposition::CMemoryLoadable {
            memory: CMemory::new(),
            base: Pointer::symbolic(Variable(839_000)),
            bytes: 16.into(),
            wide: false,
        });
        for index in 0..size {
            context = context.assume_condition(
                ConditionTerm::pointer_equal(base.clone(), pointer(830_001 + index)),
                true,
            );
        }
        let goal = Proposition::CMemoryLoadable {
            memory: CMemory::new(),
            base: base.clone(),
            bytes: 4096.into(),
            wide: false,
        };
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert!(!context.proves_atomic_without_search(&goal));
            }
        });
        samples.push(work);
    }
    eprintln!("exact alias star misses: {samples:?}");
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "{samples:?}"
    );
}

#[test]
fn indexed_storage_source_handles_displaced_aliases_beside_other_views() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = Pointer {
            block: "global:view-alias-source".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let mut query = source.clone();
        let memory = CMemory::new();
        let mut context = PureFactContext::new().assume_proposition(Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: source.clone(),
            bytes: 1024.into(),
            wide: false,
        });
        for index in 0..size {
            let next = Pointer::symbolic(Variable(840_001 + index));
            context
                .equality_graph
                .add_equality(&query.offset_by_bytes(4), &next);
            query = next;
            context = context.assume_proposition(Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: Pointer::symbolic(Variable(850_000 + index)),
                bytes: 4.into(),
                wide: false,
            });
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert!(context.proves_memory_loadable(&memory, &query, &4.into()));
                assert!(!context.proves_memory_loadable(&memory, &query, &2048.into()));
            }
        });
        samples.push(work);
    }
    eprintln!("displaced alias view checks: {samples:?}");
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "{samples:?}"
    );
}

#[test]
fn selected_alias_view_cannot_cross_distinct_allocations() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Pointer {
        block: PointerBlock::Heap(860_000),
        offset: PointerOffsetTerm::Constant(0),
    };
    let other = Pointer {
        block: PointerBlock::Heap(860_001),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new();
    // Even an inconsistent graph edge cannot turn a different allocation
    // into this source's storage during a memory query.
    let mut context = PureFactContext::new().assume_proposition(Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: source.clone(),
        bytes: 16.into(),
        wide: false,
    });
    context.equality_graph.add_equality(&source, &other);
    assert!(!context.proves_memory_loadable(&memory, &other, &8.into()));
}

#[test]
fn selected_views_follow_same_block_aliases_without_walking_the_star() {
    for wide in [false, true] {
        let mut samples = Vec::new();
        for size in [8u64, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let pointer = |id| Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(id)),
            };
            let source = pointer(870_000);
            let memory = CMemory::new();
            let extent = |n| {
                if wide {
                    Bitvector32Term::UInt64Constant(n)
                } else {
                    Bitvector32Term::Constant(n as u32)
                }
            };
            let mut context =
                PureFactContext::new().assume_proposition(Proposition::CMemoryLoadable {
                    memory: memory.clone(),
                    base: source.clone(),
                    bytes: extent(16),
                    wide,
                });
            for index in 0..size {
                context = context.assume_condition(
                    ConditionTerm::pointer_equal(source.clone(), pointer(870_001 + index)),
                    true,
                );
            }
            let query = pointer(870_000 + size);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..4 {
                    for (bytes, expected) in [(8, true), (32, false)] {
                        assert_eq!(
                            context.proves_atomic_without_search(&Proposition::CMemoryLoadable {
                                memory: memory.clone(),
                                base: query.clone(),
                                bytes: extent(bytes),
                                wide,
                            }),
                            expected
                        );
                    }
                }
            });
            samples.push(work);
        }
        eprintln!("same-block selected aliases wide={wide}: {samples:?}");
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 32),
            "{samples:?}"
        );
    }
}
