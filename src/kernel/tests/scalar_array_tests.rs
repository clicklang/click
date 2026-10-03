//! Compact scalar arrays keep checked authority independent of logical length.
use super::*;

fn pointer(block: &str, offset: i64) -> Pointer {
    Pointer {
        block: block.into(),
        offset: PointerOffsetTerm::Constant(offset),
    }
}
fn fresh(count: u32) -> CMemory {
    CMemory::new()
        .with_block("local:array-source", count * 4)
        .with_block("local:array-target", count * 4)
}
fn seeded(count: u32) -> CMemory {
    fresh(count)
        .initialize_scalar_array(
            &pointer("local:array-source", 0),
            CType::UInt32,
            count,
            CValue::UInt32(Bitvector32Term::Variable(Variable(912_345))),
            false,
        )
        .unwrap()
}

#[test]
fn compact_scalar_arrays_copy_uniform_values_without_expanding_storage_or_work() {
    let mut samples = Vec::new();
    for count in [8, 1024, 1_000_000] {
        let _session = crate::kernel::VerificationSession::enter();
        let (memory, work) = crate::instrumentation::measure_deterministic_work(|| {
            seeded(count)
                .initialize_scalar_array(
                    &pointer("local:array-target", 0),
                    CType::UInt32,
                    count,
                    CValue::pointer(pointer("local:array-source", 0)),
                    true,
                )
                .unwrap()
        });
        assert_eq!(memory.cells.concrete().len(), 0);
        assert_eq!(
            memory
                .cells
                .runs_in_block(&"local:array-source".into())
                .count(),
            1
        );
        assert_eq!(
            memory
                .cells
                .runs_in_block(&"local:array-target".into())
                .count(),
            1
        );
        assert_eq!(
            memory.load(&pointer("local:array-target", i64::from(count - 1) * 4)),
            CExpressionOutcome::Value(CValue::UInt32(Bitvector32Term::Variable(Variable(912_345))))
        );
        assert!(memory.has_initialized_bytes_at(&pointer("local:array-target", 0), count * 4));
        let mutated = memory.clone().store(
            pointer("local:array-source", 0),
            CValue::UInt32(99u32.into()),
        );
        assert_eq!(
            mutated.load(&pointer("local:array-target", 0)),
            memory.load(&pointer("local:array-target", 0))
        );
        samples.push((count, work));
    }
    eprintln!("uniform array initialization/copy (length, work): {samples:?}");
    assert!(
        samples.iter().all(|(_, work)| *work <= samples[0].1 + 32),
        "{samples:?}"
    );
}

#[test]
fn compact_scalar_arrays_reject_uninitialized_and_partial_storage() {
    let source = pointer("local:array-source", 0);
    let target = pointer("local:array-target", 0);
    assert!(
        fresh(4)
            .initialize_scalar_array(
                &target,
                CType::UInt32,
                4,
                CValue::pointer(source.clone()),
                true,
            )
            .is_err()
    );
    assert!(
        seeded(4)
            .initialize_scalar_array(
                &target,
                CType::UInt32,
                3,
                CValue::pointer(source.clone()),
                true
            )
            .is_err()
    );
    assert!(
        seeded(4)
            .initialize_scalar_array(
                &target,
                CType::Int32,
                4,
                CValue::pointer(source.clone()),
                true
            )
            .is_err()
    );
    let initialized = seeded(4)
        .initialize_scalar_array(&target, CType::UInt32, 4, CValue::pointer(source), true)
        .unwrap();
    assert!(
        initialized
            .initialize_scalar_array(
                &target,
                CType::UInt32,
                4,
                CValue::UInt32(9u32.into()),
                false
            )
            .is_err()
    );
    assert!(
        fresh(4)
            .initialize_scalar_array(
                &pointer("local:array-target", 4),
                CType::UInt32,
                3,
                CValue::UInt32(9u32.into()),
                false
            )
            .is_err()
    );
}

#[test]
fn compact_scalar_array_operations_require_complete_read_and_write_authority() {
    let source = pointer("local:array-source", 0);
    let target = pointer("local:array-target", 0);
    for copy in [false, true] {
        for complete in [false, true] {
            let mut resources = vec![own_memory_fact(
                target.clone(),
                0,
                if complete { 4 } else { 3 },
            )];
            if copy {
                resources.push(view_memory_fact(source.clone(), 0, 4));
            }
            let state = CState::new()
                .with_memory(if copy { seeded(4) } else { fresh(4) })
                .with_resource_context(ResourceContext::new().unchecked_with_facts(resources));
            let statement = c_initialize_scalar_array(
                c_pointer_value(target.clone()),
                if copy {
                    c_pointer_value(source.clone())
                } else {
                    c_uint32_literal(7)
                },
                CType::UInt32,
                4,
                copy,
            );
            let theorem = prove_c_statement_execution(state, statement).unwrap();
            let Proposition::CStatementExecutes { outcome, .. } = theorem.proposition() else {
                panic!()
            };
            if complete {
                assert!(
                    matches!(outcome, CStatementOutcome::Normal(_)),
                    "{outcome:?}"
                );
            } else {
                assert!(
                    matches!(
                        outcome,
                        CStatementOutcome::RuntimeError(CRuntimeError::MissingResource { .. })
                    ),
                    "{outcome:?}"
                );
            }
        }
    }
    let state = CState::new().with_memory(seeded(4)).with_resource_context(
        ResourceContext::new().unchecked_with_facts(vec![
            own_memory_fact(target.clone(), 0, 4),
            view_memory_fact(source.clone(), 0, 3),
        ]),
    );
    let theorem = prove_c_statement_execution(
        state,
        c_initialize_scalar_array(
            c_pointer_value(target),
            c_pointer_value(source),
            CType::UInt32,
            4,
            true,
        ),
    )
    .unwrap();
    assert!(matches!(
        theorem.proposition(),
        Proposition::CStatementExecutes {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::MissingResource { .. }),
            ..
        }
    ));
}

#[test]
fn compact_scalar_array_zero_length_needs_no_byte_authority() {
    let state = CState::new().with_memory(fresh(0));
    let statement = c_seq(
        c_initialize_scalar_array(
            c_pointer_value(pointer("local:array-source", 0)),
            c_uint32_literal(7),
            CType::UInt32,
            0,
            false,
        ),
        c_initialize_scalar_array(
            c_pointer_value(pointer("local:array-target", 0)),
            c_pointer_value(pointer("local:array-source", 0)),
            CType::UInt32,
            0,
            true,
        ),
    );
    let theorem = prove_c_statement_execution(state, statement).unwrap();
    assert!(matches!(
        theorem.proposition(),
        Proposition::CStatementExecutes {
            outcome: CStatementOutcome::Normal(_),
            ..
        }
    ));
}

#[test]
fn compact_scalar_array_initialization_rejects_readonly_storage_and_pointer_qualifiers() {
    let target = pointer("local:array-target", 0);
    for readonly_block in [false, true] {
        let memory =
            CMemory::new().with_block_or_read_only(target.block.clone(), 16, readonly_block);
        let state = CState::new()
            .with_memory(memory)
            .with_resource_context(own_memory_context(target.clone(), 0, 4));
        let pointer = CPointerValue::new(target.clone(), CType::UInt32Pointer)
            .with_pointee_constant(!readonly_block);
        let theorem = prove_c_statement_execution(
            state,
            c_initialize_scalar_array(
                CExpression::Value(CValue::Pointer(pointer)),
                c_uint32_literal(7),
                CType::UInt32,
                4,
                false,
            ),
        )
        .unwrap();
        assert!(matches!(
            theorem.proposition(),
            Proposition::CStatementExecutes {
                outcome: CStatementOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory),
                ..
            }
        ));
    }
    let theorem = prove_c_statement_execution(
        CState::new().with_memory(fresh(0)),
        c_initialize_scalar_array(
            c_pointer_value(target),
            c_void_value(),
            CType::Void,
            0,
            false,
        ),
    )
    .unwrap();
    assert!(matches!(
        theorem.proposition(),
        Proposition::CStatementExecutes {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            ..
        }
    ));
}

#[test]
fn compact_scalar_array_initialization_cannot_bypass_an_active_view_loan() {
    let target = pointer("local:array-target", 0);
    let viewed = view_memory_fact(target.clone(), 0, 4);
    let resources = ResourceContext::new()
        .unchecked_with_facts([own_memory_fact(target.clone(), 0, 4), viewed.clone()]);
    let support = resources.occurrences_for_fact(&viewed)[0];
    let ledger = crate::kernel::loans::LoanLedger::new();
    let participant = ledger.fresh_participant().unwrap();
    let opening = ledger
        .borrowed_contract_input(participant, support, viewed.clone(), None)
        .unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    let bindings = crate::kernel::loans::LoanViewBindings::default().with_inserted(
        support,
        crate::kernel::loans::LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support,
            viewed,
            hold: None,
        },
    );
    let state = CState::new()
        .with_memory(fresh(4))
        .with_resource_context(resources)
        .with_loan_ledger(Some(ledger))
        .with_loan_participant(Some(participant))
        .with_loan_view_bindings(bindings);
    for fresh in [true, false] {
        let statement = if fresh {
            c_initialize_scalar_array(
                c_pointer_value(target.clone()),
                c_uint32_literal(7),
                CType::UInt32,
                4,
                false,
            )
        } else {
            c_write_scalar_array_region(
                c_pointer_value(target.clone()),
                c_uint32_literal(7),
                CType::UInt32,
                4,
                false,
            )
        };
        let theorem = prove_c_statement_execution(state.clone(), statement).unwrap();
        assert!(matches!(
            theorem.proposition(),
            Proposition::CStatementExecutes {
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(_)),
                ..
            }
        ));
    }
}

#[test]
fn compact_array_regions_copy_and_overwrite_preserve_neighbors_and_scale() {
    let mut samples = Vec::new();
    for count in [4, 1024, 1_000_000] {
        let _session = crate::kernel::VerificationSession::enter();
        let bytes = count * 4;
        let source = pointer("local:region-source", 4);
        let target = pointer("local:region-target", 4);
        let context = PureFactContext::new();
        let (memory, work) = crate::instrumentation::measure_deterministic_work(|| {
            let memory = CMemory::new()
                .with_block(source.block.clone(), bytes + 8)
                .with_block(target.block.clone(), bytes + 8)
                .store(
                    pointer("local:region-target", 0),
                    CValue::UInt32(11u32.into()),
                )
                .store(
                    pointer("local:region-target", i64::from(bytes) + 4),
                    CValue::UInt32(17u32.into()),
                )
                .write_scalar_array_region(
                    &source,
                    CType::UInt32,
                    count,
                    CValue::UInt32(7u32.into()),
                    false,
                    false,
                    &context,
                )
                .unwrap()
                .write_scalar_array_region(
                    &target,
                    CType::UInt32,
                    count,
                    CValue::UInt32(99u32.into()),
                    false,
                    false,
                    &context,
                )
                .unwrap();
            memory
                .write_scalar_array_region(
                    &target,
                    CType::UInt32,
                    count,
                    CValue::pointer(source.clone()),
                    true,
                    false,
                    &context,
                )
                .unwrap()
        });
        for (offset, value) in [
            (0, 11),
            (4, 7),
            (i64::from(bytes), 7),
            (i64::from(bytes) + 4, 17),
        ] {
            assert_eq!(
                memory.load(&pointer("local:region-target", offset)),
                CExpressionOutcome::Value(CValue::UInt32(value.into()))
            );
        }
        assert_eq!(memory.cells.concrete().len(), 2);
        assert_eq!(memory.cells.runs_in_block(&target.block).count(), 1);
        assert!(memory.has_initialized_bytes_at(&target, bytes));
        let mutated = memory.store(source, CValue::UInt32(101u32.into()));
        assert_eq!(
            mutated.load(&target),
            CExpressionOutcome::Value(CValue::UInt32(7u32.into()))
        );
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "{samples:?}"
    );
}

#[test]
fn compact_array_regions_check_source_type_extent_alignment_and_initialization() {
    let context = PureFactContext::new();
    let source = pointer("local:source", 4);
    let target = pointer("local:target", 4);
    let memory = CMemory::new()
        .with_block(source.block.clone(), 24)
        .with_block(target.block.clone(), 24)
        .write_scalar_array_region(
            &source,
            CType::UInt32,
            4,
            CValue::UInt32(7u32.into()),
            false,
            false,
            &context,
        )
        .unwrap();
    for (at, element, count) in [
        (target.clone(), CType::Int32, 4),
        (pointer("local:target", 5), CType::UInt32, 4),
        (pointer("local:target", i64::MAX - 3), CType::UInt32, 4),
        (target.clone(), CType::UInt32, 6),
    ] {
        assert!(
            memory
                .clone()
                .write_scalar_array_region(
                    &at,
                    element,
                    count,
                    CValue::pointer(source.clone()),
                    true,
                    false,
                    &context
                )
                .is_err()
        );
    }
    let changed = memory
        .clone()
        .store(source.clone(), CValue::UInt32(9u32.into()));
    let copied = changed
        .write_scalar_array_region(
            &target,
            CType::UInt32,
            4,
            CValue::pointer(source.clone()),
            true,
            false,
            &context,
        )
        .unwrap();
    assert_eq!(
        copied.load(&target),
        CExpressionOutcome::Value(CValue::UInt32(9u32.into()))
    );
    let fresh = CMemory::new()
        .with_block(source.block.clone(), 24)
        .with_block(target.block.clone(), 24);
    assert!(
        fresh
            .write_scalar_array_region(
                &target,
                CType::UInt32,
                4,
                CValue::pointer(source.clone()),
                true,
                false,
                &context
            )
            .is_err()
    );
    // Reading the old uniform value first makes overlapping/self copies snapshots.
    let copied = memory
        .write_scalar_array_region(
            &pointer("local:source", 8),
            CType::UInt32,
            3,
            CValue::pointer(source),
            true,
            false,
            &context,
        )
        .unwrap();
    assert_eq!(
        copied.load(&pointer("local:source", 16)),
        CExpressionOutcome::Value(CValue::UInt32(7u32.into()))
    );
}

#[test]
fn compact_array_region_execution_requires_full_authority_and_mutable_storage() {
    for (writable, complete, readonly) in [
        (true, true, false),
        (true, false, false),
        (false, true, false),
        (true, true, true),
    ] {
        let target = pointer("local:region", 4);
        let resource = if writable {
            own_memory_fact(target.clone(), 0, if complete { 4 } else { 3 })
        } else {
            view_memory_fact(target.clone(), 0, 4)
        };
        let state = CState::new()
            .with_memory(CMemory::new().with_block_or_read_only(target.block.clone(), 24, readonly))
            .with_resource_context(ResourceContext::new().unchecked_with_facts(vec![resource]));
        let statement = c_write_scalar_array_region(
            c_pointer_value(target),
            c_uint32_literal(7),
            CType::UInt32,
            4,
            false,
        );
        let theorem = prove_c_statement_execution(state, statement).unwrap();
        let Proposition::CStatementExecutes { outcome, .. } = theorem.proposition() else {
            panic!()
        };
        assert_eq!(
            matches!(outcome, CStatementOutcome::Normal(_)),
            writable && complete && !readonly
        );
    }
}

#[test]
fn compact_array_region_write_refreshes_an_addressed_scalar_local() {
    let declaration = prove_c_statement_execution(
        CState::new(),
        c_seq(
            c_declare("value", CType::UInt32),
            c_assign("value", c_uint32_literal(42)),
        ),
    )
    .unwrap();
    let Proposition::CStatementExecutes {
        outcome: CStatementOutcome::Normal(state),
        ..
    } = declaration.proposition()
    else {
        panic!("scalar declaration must execute");
    };
    let target = state.locals().slot("value").unwrap().clone();
    let state = state.clone().with_resource_context(
        ResourceContext::new().unchecked_with_facts([own_memory_fact(target, 0, 1)]),
    );
    let theorem = prove_c_statement_execution(
        state,
        c_write_scalar_array_region(
            c_addr_of("value"),
            c_uint32_literal(7),
            CType::UInt32,
            1,
            false,
        ),
    )
    .unwrap();
    let Proposition::CStatementExecutes {
        outcome: CStatementOutcome::Normal(state),
        ..
    } = theorem.proposition()
    else {
        panic!("authorized region write must execute");
    };
    assert_eq!(
        state.locals().get("value"),
        Some(&CValue::UInt32(7u32.into()))
    );
}

#[test]
fn scalar_array_snapshots_preserve_sparse_lanes_without_extent_work() {
    let mut samples = Vec::new();
    for count in [8, 1024, 1_000_000] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = pointer("local:array-source", 0);
        let target = pointer("local:array-target", 0);
        let lane = CValue::UInt32(Bitvector32Term::Variable(Variable(912_346)));
        let memory = seeded(count).store(source.clone(), lane.clone()).store(
            pointer("local:array-source", i64::from(count - 1) * 4),
            CValue::UInt32(17u32.into()),
        );
        let (copied, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory
                .initialize_scalar_array(
                    &target,
                    CType::UInt32,
                    count,
                    CValue::pointer(source.clone()),
                    true,
                )
                .unwrap()
        });
        assert_eq!(copied.cells.concrete().len(), 4);
        assert_eq!(copied.cells.runs_in_block(&target.block).count(), 1);
        assert_eq!(
            copied.load(&target),
            CExpressionOutcome::Value(lane.clone())
        );
        assert_eq!(
            copied.load(&pointer("local:array-target", i64::from(count - 1) * 4)),
            CExpressionOutcome::Value(CValue::UInt32(17u32.into()))
        );
        let changed = copied
            .store(source.clone(), CValue::UInt32(99u32.into()))
            .store(
                pointer("local:array-target", 4),
                CValue::UInt32(18u32.into()),
            );
        assert_eq!(changed.load(&target), CExpressionOutcome::Value(lane));
        assert_eq!(
            changed.load(&pointer("local:array-source", 4)),
            CExpressionOutcome::Value(CValue::UInt32(Bitvector32Term::Variable(Variable(912_345))))
        );
        samples.push((count, work));
    }
    eprintln!("sparse snapshot copy (length, work): {samples:?}");
    assert!(
        samples.iter().all(|(_, work)| *work <= samples[0].1 + 32),
        "{samples:?}"
    );
}

#[test]
fn scalar_array_snapshots_check_explicit_coverage_types_and_overlap() {
    let source = pointer("local:array-source", 0);
    let target = pointer("local:array-target", 0);
    let mut memory = fresh(4);
    for index in 0..4 {
        memory = memory.store(
            pointer("local:array-source", index * 4),
            CValue::UInt32((index as u32 + 1).into()),
        );
    }
    let copied = memory
        .clone()
        .initialize_scalar_array(
            &target,
            CType::UInt32,
            4,
            CValue::pointer(source.clone()),
            true,
        )
        .unwrap();
    for index in 0..4 {
        assert_eq!(
            copied.load(&pointer("local:array-target", index * 4)),
            CExpressionOutcome::Value(CValue::UInt32((index as u32 + 1).into()))
        );
    }
    let overlap = memory
        .clone()
        .write_scalar_array_region(
            &pointer("local:array-source", 4),
            CType::UInt32,
            3,
            CValue::pointer(source.clone()),
            true,
            false,
            &PureFactContext::new(),
        )
        .unwrap();
    for index in 1..4 {
        assert_eq!(
            overlap.load(&pointer("local:array-source", index * 4)),
            CExpressionOutcome::Value(CValue::UInt32((index as u32).into()))
        );
    }
    let wrong_type = memory
        .clone()
        .store(pointer("local:array-source", 4), CValue::Int32(2.into()));
    let missing = fresh(4).store(source.clone(), CValue::UInt32(1u32.into()));
    let misaligned = memory.store(pointer("local:array-source", 1), CValue::UInt8(3u32.into()));
    for invalid in [wrong_type, missing, misaligned] {
        assert!(
            invalid
                .initialize_scalar_array(
                    &target,
                    CType::UInt32,
                    4,
                    CValue::pointer(source.clone()),
                    true
                )
                .is_err()
        );
    }
}

#[test]
fn scalar_array_snapshot_region_does_not_scan_unrelated_sibling_cells() {
    let mut samples = Vec::new();
    for siblings in [1, 64, 2048] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = pointer("local:siblings", 4);
        let target = pointer("local:target", 0);
        let mut memory = CMemory::new()
            .with_block(source.block.clone(), (siblings + 5) * 4)
            .with_block(target.block.clone(), 16)
            .write_scalar_array_region(
                &source,
                CType::UInt32,
                4,
                CValue::UInt32(7u32.into()),
                false,
                false,
                &PureFactContext::new(),
            )
            .unwrap()
            .store(source.clone(), CValue::UInt32(9u32.into()));
        for index in 0..siblings {
            memory = memory.store(
                pointer("local:siblings", i64::from(index + 5) * 4),
                CValue::UInt32(11u32.into()),
            );
        }
        let (copied, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory
                .write_scalar_array_region(
                    &target,
                    CType::UInt32,
                    4,
                    CValue::pointer(source),
                    true,
                    false,
                    &PureFactContext::new(),
                )
                .unwrap()
        });
        assert_eq!(
            copied.load(&target),
            CExpressionOutcome::Value(CValue::UInt32(9u32.into()))
        );
        samples.push((siblings, work));
    }
    assert!(
        samples.iter().all(|(_, work)| *work <= samples[0].1 + 128),
        "{samples:?}"
    );
}
