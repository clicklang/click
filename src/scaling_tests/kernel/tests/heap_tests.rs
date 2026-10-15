// Scaling tests of `src/kernel/tests/heap_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn aliased_read_validity_lookup_ignores_unrelated_facts() {
    let memory = CMemory::new();
    let pointer = Pointer {
        block: PointerBlock::Heap(941_000),
        offset: PointerOffsetTerm::Constant(0),
    };
    let alias = Pointer::symbolic(Variable(941_001));
    let validity = Proposition::CMemoryReadDefined {
        memory: memory.clone(),
        pointer: pointer.offset_by_bytes(4),
        value_type: CType::Int32,
    };
    let field_alias = alias.offset_by_bytes(4);
    let mut samples = Vec::new();
    for count in [0, 16, 64, 256] {
        let mut assumptions = PureFactContext::new()
            .assume_proposition(validity.clone())
            .assume_proposition(Proposition::ConditionIs(
                ConditionTerm::pointer_equal(alias.clone(), pointer.clone()),
                true,
            ));
        for index in 1..=count {
            assumptions = assumptions.assume_proposition(Proposition::CMemoryReadDefined {
                memory: memory.clone(),
                pointer: Pointer {
                    block: PointerBlock::Heap(942_000 + index),
                    offset: PointerOffsetTerm::Constant(0),
                },
                value_type: CType::Int32,
            });
        }
        let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
            assumptions.has_memory_read_defined_evidence(&memory, &field_alias, CType::Int32)
        });
        assert!(proved);
        samples.push(work);
        assert!(
            !assumptions
                .without_exact_fact(&validity)
                .has_memory_read_defined_evidence(&memory, &field_alias, CType::Int32)
        );
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 16),
        "{samples:?}"
    );
}

#[test]
fn read_validity_lookup_ignores_unrelated_cells() {
    let memory = CMemory::new();
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let validity = Proposition::CMemoryReadDefined {
        memory: memory.clone(),
        pointer: pointer.clone(),
        value_type: CType::Int32,
    };
    let mut samples = Vec::new();
    for count in [0, 16, 64, 256] {
        let mut assumptions = PureFactContext::new().assume_proposition(validity.clone());
        for index in 1..=count {
            assumptions = assumptions.assume_proposition(Proposition::CMemoryReadDefined {
                memory: memory.clone(),
                pointer: Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::Constant(index * 4),
                },
                value_type: CType::Int32,
            });
        }
        let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
            assumptions.has_memory_read_defined_evidence(&memory, &pointer, CType::Int32)
        });
        assert!(proved);
        samples.push(work);
        assert!(
            !assumptions
                .without_exact_fact(&validity)
                .has_memory_read_defined_evidence(&memory, &pointer, CType::Int32)
        );
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 16),
        "{samples:?}"
    );
}

#[test]
fn unknown_read_validity_does_not_resolve_unrelated_cells() {
    let target = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(770))),
            byte_width: 4,
        },
    };
    let mut samples = Vec::new();
    for count in [0, 16, 64, 256] {
        let mut memory = CMemory::new();
        for index in 0..count {
            memory = memory.store(
                Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::Constant(index * 4),
                },
                int32(index as u32),
            );
        }
        let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
            PureFactContext::new().proves_memory_read_defined(&memory, &target, CType::Int32)
        });
        assert!(!proved);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 16),
        "{samples:?}"
    );
}

#[test]
fn defined_read_survives_failed_allocation_after_an_unrelated_store() {
    let address = Pointer {
        block: PointerBlock::Heap(9100),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut samples = Vec::new();
    for count in [8, 16, 32, 64] {
        let mut memory = CMemory::new().with_block(address.block.clone(), 4);
        for index in 0..count {
            memory = memory.store(
                Pointer {
                    block: PointerBlock::Heap(9200 + index),
                    offset: PointerOffsetTerm::Constant(0),
                },
                int32(1),
            );
        }
        let fact = Proposition::CMemoryReadDefined {
            memory: memory.clone(),
            pointer: address.clone(),
            value_type: CType::Int32,
        };
        let assumptions = PureFactContext::new().assume_proposition(fact);
        let request = Pointer {
            block: PointerBlock::Symbolic(Variable(9300)),
            offset: PointerOffsetTerm::Constant(0),
        };
        let pending = memory.with_pending_heap_allocation(
            request.clone(),
            Bitvector32Term::Constant(4),
            false,
        );
        // C assigns malloc's result before branching on it. That intervening
        // store prevents failure from merely interning back to the old memory.
        let pending = pending.store(
            Pointer {
                block: "local:result".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            CValue::pointer(request.clone()),
        );
        let (failed, _, _) = pending
            .resolve_pending_heap_allocation(&request, false)
            .unwrap();
        let goal = Proposition::CMemoryReadDefined {
            memory: failed.clone(),
            pointer: address.clone(),
            value_type: CType::Int32,
        };
        let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::PureFactContext::settles_exactly(&assumptions, &goal)
        });
        assert!(proved, "failure to allocate must preserve an existing read");
        samples.push(work);
        let changed = failed.with_call_memory_havoc(
            Variable(9301),
            &[CMemoryRange::new(
                address.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )],
            &assumptions,
            None,
        );
        assert!(!assumptions.has_memory_read_defined_evidence(&changed, &address, CType::Int32));
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 16),
        "{samples:?}"
    );
}

#[test]
fn free_allocation_discovery_ignores_unrelated_resource_tokens() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer::symbolic(Variable(948_000));
    let mut samples = Vec::new();
    for count in [0, 16, 64, 256] {
        let mut resources = ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own_allocation(base.clone(), 16))
            .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                base.clone(),
                0.into(),
                4.into(),
            )));
        for index in 0..count {
            resources = resources.unchecked_with_fact(CResourceFact::own_allocation(
                Pointer {
                    block: PointerBlock::Heap(948_100 + index),
                    offset: PointerOffsetTerm::Constant(0),
                },
                16,
            ));
        }
        let state = CState::new()
            .with_resource_context(resources)
            .with_local("p", CValue::pointer(base.clone()));
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            execute_c_statement_paths(
                &state,
                &c_heap_free(c_variable("p")),
                &PureFactContext::new(),
                CExecutionContext::execute_bodies(&CExecutionEnvironment::new()),
                &mut ExecutionBudget::default(),
            )
            .expect("selected declared allocation should free")
        });
        let [
            CStatementExecutionPath {
                outcome: CStatementOutcome::Normal(after),
                ..
            },
        ] = paths.as_slice()
        else {
            panic!("expected one successful free: {paths:?}");
        };
        assert!(
            after
                .memory()
                .is_deallocated_heap_address(&base, &PureFactContext::new())
        );
        assert_eq!(after.resources().facts().len(), count as usize);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 32),
        "{samples:?}"
    );
}

#[test]
fn realloc_reference_check_ignores_unrelated_resource_tokens() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut samples = Vec::new();
    for count in [0, 16, 64, 256] {
        let state = successful_heap_allocation_state();
        let mut resources = state.resources().clone();
        for index in 0..count {
            resources = resources.unchecked_with_fact(CResourceFact::own_allocation(
                Pointer {
                    block: PointerBlock::Heap(949_100 + index),
                    offset: PointerOffsetTerm::Constant(0),
                },
                16,
            ));
        }
        let state = state
            .with_resource_context(resources)
            .with_local("q", CValue::pointer(Pointer::null()));
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            execute_c_statement_paths(
                &state,
                &c_call_assign("q", "realloc", vec![c_variable("p"), c_int32_literal(8)]),
                &PureFactContext::new(),
                CExecutionContext::execute_bodies(&CExecutionEnvironment::new()),
                &mut ExecutionBudget::default(),
            )
            .expect("reallocation should produce a pending result")
        });
        assert!(
            matches!(
                paths.as_slice(),
                [CStatementExecutionPath {
                    outcome: CStatementOutcome::Normal(_),
                    ..
                }]
            ),
            "{paths:?}"
        );
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 32),
        "{samples:?}"
    );
}
