// Scaling tests of `src/kernel/proof/equality_rewrite.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn pointer_rewrite_integer_reads_preserves_snapshot_kind_and_scales() {
    for same_block in [false, true] {
        let mut samples = Vec::new();
        for size in [4u64, 16, 64, 256] {
            let _session = VerificationSession::enter();
            let mut p = Pointer::symbolic(Variable(241_000));
            let mut q = Pointer::symbolic(Variable(241_001)).offset_by_bytes(3);
            if same_block {
                p.offset =
                    PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(241_002)), 1);
                q.block = p.block.clone();
                q.offset =
                    PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(241_003)), 1);
            }
            let cited =
                Proposition::ConditionIs(ConditionTerm::pointer_equal(p.clone(), q.clone()), true);
            let mut memory = CMemory::new();
            let mut facts = ProofFacts::default().with_fact(cited.clone());
            for index in 0..size {
                memory = memory.store(
                    Pointer::symbolic(Variable(242_000 + index)),
                    CValue::UInt8(Bitvector32Term::Constant(7)),
                );
                facts = facts.with_fact(integer_equality(
                    IntegerTerm::var(Variable(244_000 + index)),
                    IntegerTerm::constant_i64(index as i64),
                ));
            }
            let read = |memory: &CMemory, pointer: &Pointer, kind| {
                Bitvector32Term::Variable(crate::kernel::eval::load_variable_for_exact_cell(
                    &crate::kernel::intern_c_memory(memory.clone()),
                    pointer,
                    kind,
                    1,
                ))
            };
            // The read identity preserves only its original cell. The observed
            // origin is needed when the equality exposes the alias address.
            let source =
                Bitvector32Term::Variable(crate::kernel::load_variable_for_cell_with_origin(
                    &crate::kernel::intern_c_memory(CMemory::new()),
                    &p,
                    LoadKind::UInt8,
                    1,
                    &crate::kernel::intern_c_memory(memory.clone()),
                ));
            let target = read(&memory, &q, LoadKind::UInt8);
            let later = memory
                .clone()
                .store(q.clone(), CValue::UInt8(Bitvector32Term::Constant(99)));
            let other_snapshot = read(&later, &q, LoadKind::UInt8);
            let other_kind = read(&memory, &q, LoadKind::Int8);
            let mut work = 0;
            for ty in [
                MachineIntegerType::Int32,
                MachineIntegerType::UInt32,
                MachineIntegerType::Int64,
                MachineIntegerType::UInt64,
            ] {
                let observation =
                    |value| IntegerTerm::Machine(SharedMachineIntegerTerm::intern(ty, value));
                let goal =
                    integer_equality(observation(source.clone()), IntegerTerm::constant_i64(0));
                let expected =
                    integer_equality(observation(target.clone()), IntegerTerm::constant_i64(0));
                let (checked, cost) = crate::instrumentation::measure_deterministic_work(|| {
                    facts.check_equality_rewrite(&goal, &cited)
                });
                let checked = checked.unwrap();
                assert_eq!(checked.proposition(), &expected);
                assert_ne!(
                    checked.proposition(),
                    &integer_equality(
                        observation(other_snapshot.clone()),
                        IntegerTerm::constant_i64(0)
                    )
                );
                assert_ne!(
                    checked.proposition(),
                    &integer_equality(
                        observation(other_kind.clone()),
                        IntegerTerm::constant_i64(0)
                    )
                );
                assert!(
                    ProofFacts::default()
                        .check_equality_rewrite(&goal, &cited)
                        .is_err()
                );
                work += cost;
            }
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[0] == pair[1]),
            "{samples:?}"
        );
    }
}

/// Rewriting a field owner changes a typed read's address, not the
/// loaded value's legacy storage-relative offset. Exercise cold reads
/// with growing unrelated snapshots and premises, plus ordinary indexing.
#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn pointer_read_rewrite_preserves_value_snapshot_and_scales() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let owner = Pointer::symbolic(Variable(211_000));
        let alias = Pointer {
            block: PointerBlock::Symbolic(Variable(211_001)),
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(211_002)), 4),
        };
        let address = owner.offset_by_bytes(16);
        let alias_address = alias.offset_by_bytes(16);
        let cited = Proposition::ConditionIs(
            ConditionTerm::pointer_equal(owner.clone(), alias.clone()),
            true,
        );
        let mut facts = ProofFacts::default().with_fact(cited.clone());
        let mut memory = CMemory::new();
        for i in 0..size {
            memory = memory.store(
                Pointer::symbolic(Variable(220_000 + i)),
                CValue::Int32(Bitvector32Term::Constant(7)),
            );
            facts = facts.with_fact(equality(
                Bitvector32Term::Variable(Variable(230_000 + i)),
                Bitvector32Term::Constant(i as u32),
            ));
        }
        let context = PureFactContext::new();
        let read = |memory: &CMemory, address: &Pointer| {
            let paths = crate::kernel::eval::evaluate_logical_memory_load_paths(
                memory,
                address.clone(),
                CType::Int32Pointer,
                Default::default(),
                Vec::new(),
                &context,
            );
            let [path] = paths.as_slice() else {
                panic!("one logical read");
            };
            assert!(!path.facts.has_path_conditions() && path.obligations.is_empty());
            let crate::kernel::CExpressionOutcome::Value(CValue::Pointer(value)) = &path.outcome
            else {
                panic!("typed pointer read");
            };
            value.pointer().clone()
        };
        let original = read(&memory, &address);
        let leaf = Pointer::symbolic(Variable(211_003));
        let goal = Proposition::ConditionIs(
            ConditionTerm::pointer_equal(original.clone(), leaf.clone()),
            true,
        );
        assert!(
            ProofFacts::default()
                .check_equality_rewrite(&goal, &cited)
                .is_err()
        );
        let ((rewritten, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                facts.check_equality_rewrite(&goal, &cited).unwrap()
            })
        });
        let Proposition::ConditionIs(ConditionTerm::PointerEqual(actual, rhs), true) =
            rewritten.proposition()
        else {
            panic!("full pointer equality retained");
        };
        assert_eq!(rhs.as_ref(), &leaf);
        assert_eq!(actual.offset, PointerOffsetTerm::Constant(0));
        let expected = read(&memory, &alias_address);
        assert!(context.pointers_known_equal(actual, &expected));
        assert!(!ResourceContext::new().permits_memory_read(&alias_address, 8, &context));
        let replacement = Pointer::symbolic(Variable(211_004));
        let later = memory.clone().store(
            alias_address.clone(),
            CValue::typed_pointer(replacement.clone(), CType::Int32Pointer),
        );
        assert_eq!(read(&later, &alias_address), replacement);
        assert!(!context.pointers_known_equal(actual, &replacement));
        // A read created after the store must rewrite to the new pointer,
        // while the previously rewritten read above retains its snapshot.
        let stored_goal = Proposition::ConditionIs(
            ConditionTerm::pointer_equal(read(&later, &address), replacement.clone()),
            true,
        );
        let stored_rewrite = facts.check_equality_rewrite(&stored_goal, &cited).unwrap();
        assert_eq!(
            stored_rewrite.proposition(),
            &Proposition::ConditionIs(
                ConditionTerm::pointer_equal(replacement.clone(), replacement),
                true,
            )
        );
        // An unregistered scaled integer is still pointer arithmetic.
        let index = Bitvector32Term::Variable(Variable(211_005));
        let indexed = Pointer::loaded(owner.block.clone(), index.clone(), 4);
        let arithmetic_goal =
            Proposition::ConditionIs(ConditionTerm::pointer_equal(indexed, leaf.clone()), true);
        let arithmetic = facts
            .check_equality_rewrite(&arithmetic_goal, &cited)
            .unwrap();
        let expected_indexed = alias.offset_by_int32_elements(index);
        assert_eq!(
            arithmetic.proposition(),
            &Proposition::ConditionIs(ConditionTerm::pointer_equal(expected_indexed, leaf), true,)
        );
        samples.push((work, map_work));
    }
    assert!(
        samples.iter().all(|sample| sample.0 <= samples[0].0 + 128),
        "{samples:?}"
    );
    assert!(
        samples.iter().all(|sample| sample.1 <= samples[0].1 + 1024),
        "{samples:?}"
    );
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn native_equality_rewrite_preserves_wide_order_and_truth_value() {
    let x = Bitvector32Term::Variable(Variable(193_020));
    let y = Bitvector32Term::Variable(Variable(193_021));
    let cited = Proposition::ConditionIs(
        ConditionTerm::Bitvector64Equal(Box::new(x.clone()), Box::new(y.clone())),
        true,
    );
    // The same immutable ambient sets exercise every order/truth case.
    // Build them once so fixture setup does not dominate this gate test.
    let fact_sets: Vec<_> = [0, 16, 64, 256, 1024]
        .into_iter()
        .map(|ambient| {
            let mut facts = ProofFacts::default().with_fact(cited.clone());
            for i in 0..ambient {
                facts = facts.with_fact(equality(
                    Bitvector32Term::Variable(Variable(194_000 + i)),
                    Bitvector32Term::Constant(i as u32),
                ));
            }
            facts
        })
        .collect();
    let comparisons = [
        ConditionTerm::Bitvector64SignedLessThan
            as fn(Box<Bitvector32Term>, Box<Bitvector32Term>) -> ConditionTerm,
        ConditionTerm::Bitvector64SignedLessEqual,
        ConditionTerm::Bitvector64SignedGreaterThan,
        ConditionTerm::Bitvector64SignedGreaterEqual,
        ConditionTerm::Bitvector64UnsignedLessThan,
        ConditionTerm::Bitvector64UnsignedLessEqual,
        ConditionTerm::Bitvector64UnsignedGreaterThan,
        ConditionTerm::Bitvector64UnsignedGreaterEqual,
    ];
    for make in comparisons {
        for bound in [
            Bitvector32Term::Int64Constant(i64::MIN),
            Bitvector32Term::UInt64Constant(u64::MAX),
        ] {
            for truth in [false, true] {
                let goal = Proposition::ConditionIs(
                    make(Box::new(x.clone()), Box::new(bound.clone())),
                    truth,
                );
                let expected = Proposition::ConditionIs(
                    make(Box::new(y.clone()), Box::new(bound.clone())),
                    truth,
                );
                assert!(
                    ProofFacts::default()
                        .check_equality_rewrite(&goal, &cited)
                        .is_err()
                );
                let mut costs = Vec::new();
                for facts in &fact_sets {
                    let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                        facts.check_equality_rewrite(&goal, &cited)
                    });
                    let mut checked = result.unwrap();
                    assert_eq!(checked.proposition(), &expected);
                    let forged = Proposition::ConditionIs(
                        make(Box::new(y.clone()), Box::new(bound.clone())),
                        !truth,
                    );
                    assert!(!checked.try_present_as(&forged));
                    assert_eq!(checked.proposition(), &expected);
                    costs.push(work);
                }
                assert!(
                    costs[0] > 0 && costs.iter().all(|cost| *cost == costs[0]),
                    "{costs:?}"
                );
            }
        }
    }
}

#[test]
#[ignore = "nightly: 1.9s in the parallel gate"]
fn native_integer_bound_rewrite_is_dag_linear_and_budget_checked() {
    let x = Bitvector32Term::Variable(Variable(193_028));
    let y = Bitvector32Term::Variable(Variable(193_029));
    let cited = equality(x.clone(), y.clone());
    let make_term = |value, depth| {
        let mut term: SharedIntegerTerm =
            IntegerTerm::from_machine(MachineIntegerType::UInt32, value)
                .unwrap()
                .into();
        for _ in 0..depth {
            term = IntegerTerm::add(term.as_ref().clone(), term.as_ref().clone()).into();
        }
        term
    };
    let condition = |term| {
        Proposition::ConditionIs(
            ConditionTerm::IntegerLessEqual(term, IntegerTerm::constant_i64(4294967295).into()),
            true,
        )
    };
    let mut depth_costs = Vec::new();
    for depth in [4, 8, 16, 32] {
        let goal = condition(make_term(x.clone(), depth));
        let expected = condition(make_term(y.clone(), depth));
        let mut ambient_costs = Vec::new();
        for ambient in [0, 16, 64, 256, 1024] {
            let mut facts = ProofFacts::default().with_fact(cited.clone());
            for i in 0..ambient {
                facts = facts.with_fact(equality(
                    Bitvector32Term::Variable(Variable(195_000 + i)),
                    Bitvector32Term::Constant(i as u32),
                ));
            }
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.check_equality_rewrite(&goal, &cited)
            });
            assert_eq!(result.unwrap().proposition(), &expected);
            ambient_costs.push(work);
        }
        assert!(
            ambient_costs[0] > 0 && ambient_costs.iter().all(|cost| *cost == ambient_costs[0]),
            "{ambient_costs:?}"
        );
        depth_costs.push(ambient_costs[0]);
    }
    assert!(depth_costs[3] <= depth_costs[0] * 10, "{depth_costs:?}");
    let facts = ProofFacts::default().with_fact(cited.clone());
    let result = crate::instrumentation::with_run_work_limit(0, || {
        facts.check_equality_rewrite(&condition(make_term(x, 32)), &cited)
    });
    assert!(
        result.is_err(),
        "an exhausted rewrite must not emit a partial refinement"
    );
}

#[test]
fn integer_equality_rewrite_scales_with_selected_dag_not_ambient_facts() {
    let x = IntegerTerm::var(Variable(193_021));
    let y = IntegerTerm::var(Variable(193_022));
    let cited = integer_equality(x.clone(), y.clone());
    let mut costs = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let mut facts = ProofFacts::default().with_fact(cited.clone());
        for i in 0..size {
            facts = facts.with_fact(integer_equality(
                IntegerTerm::var(Variable(194_000 + i as u64)),
                IntegerTerm::constant_i64(i as i64),
            ));
        }
        let small = integer_equality(IntegerTerm::multiply(x.clone(), x.clone()), y.clone());
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.check_equality_rewrite(&small, &cited)
        });
        checked.unwrap();
        costs.push(work);
        // Repeated squaring has exponentially many paths but a linear DAG.
        let mut term: SharedIntegerTerm = x.clone().into();
        for _ in 0..size {
            term = IntegerTerm::Multiply(term.clone(), term).into();
        }
        let goal = integer_equality(term.as_ref().clone(), y.clone());
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.check_equality_rewrite(&goal, &cited)
        });
        let checked = checked.unwrap();
        assert!(work <= 20 * size + 100, "size {size}: {work}");
        let Proposition::ConditionIs(ConditionTerm::IntegerEqual(mut root, _), true) =
            checked.proposition().clone()
        else {
            unreachable!()
        };
        for _ in 0..size {
            let IntegerTerm::Multiply(a, b) = root.as_ref() else {
                unreachable!()
            };
            assert_eq!(a.id(), b.id());
            root = a.clone();
        }
        assert_eq!(root.as_ref(), &y);
    }
    assert!(costs.iter().all(|work| *work == costs[0]), "{costs:?}");
}

#[test]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn cited_read_rewrite_requires_unchanged_cells_and_its_named_premise() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Pointer {
        block: "rewrite-selected-read".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    crate::kernel::eval::declare_load_access_width(&pointer, 4);
    let before = CMemory::new().with_block("rewrite-selected-read", 4);
    let after = before.clone().with_block("local:rewrite-unrelated", 4);
    let changed = after.clone().store(
        pointer.clone(),
        CValue::Int32(Bitvector32Term::Constant(43)),
    );
    let load = |memory: &CMemory| {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(memory),
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Bits32,
        )
    };
    let premise = equality(load(&before), Bitvector32Term::Constant(42));
    let goal = equality(load(&after), Bitvector32Term::Constant(42));
    let mut costs = vec![];
    for size in [16u64, 64, 256, 1024] {
        let mut facts = ProofFacts::from_ordered(std::slice::from_ref(&premise));
        for index in 0..size {
            facts = facts.with_fact(equality(
                Bitvector32Term::Variable(Variable(80_000 + index)),
                Bitvector32Term::Constant(index as u32),
            ));
        }
        crate::kernel::eval::clear_load_canonicalization_caches();
        let (rewritten, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.check_equality_rewrite(&goal, &premise)
        });
        assert_eq!(
            rewritten.unwrap().proposition(),
            &equality(Bitvector32Term::Constant(42), Bitvector32Term::Constant(42))
        );
        assert!(
            facts
                .check_equality_rewrite(
                    &equality(load(&changed), Bitvector32Term::Constant(42)),
                    &premise
                )
                .is_err()
        );
        costs.push(work);
    }
    assert!(costs.iter().all(|work| *work <= 8), "{costs:?}");
    assert!(
        ProofFacts::default()
            .check_equality_rewrite(&goal, &premise)
            .is_err()
    );
}

#[test]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn same_block_pointer_view_rewrite_preserves_extent_and_selected_work() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(192_920)), 1);
    let target = PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(192_921)), 1);
    let cited = Proposition::ConditionIs(
        ConditionTerm::PointerOffsetEqual(Box::new(source.clone()), Box::new(target.clone())),
        true,
    );
    let memory = CMemory::new().with_block("offset-view-rewrite", 8);
    let extent = Bitvector32Term::Variable(Variable(192_922));
    let goal = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::add(source, PointerOffsetTerm::Constant(2)),
        },
        bytes: extent.clone(),
        wide: false,
    };
    assert!(
        ProofFacts::default()
            .check_equality_rewrite(&goal, &cited)
            .is_err()
    );
    let false_equality = match &cited {
        Proposition::ConditionIs(condition, _) => {
            Proposition::ConditionIs(condition.clone(), false)
        }
        _ => unreachable!(),
    };
    let false_facts = ProofFacts::from_ordered(&[false_equality]);
    assert!(false_facts.check_equality_rewrite(&goal, &cited).is_err());
    let mut costs = Vec::new();
    for size in [0, 16, 64, 256, 1024] {
        let mut facts = ProofFacts::from_ordered(std::slice::from_ref(&cited));
        for index in 0..size {
            facts = facts.with_fact(equality(
                Bitvector32Term::Variable(Variable(210_000 + index)),
                Bitvector32Term::Constant(index as u32),
            ));
        }
        let (rewritten, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.check_equality_rewrite(&goal, &cited).unwrap()
        });
        let Proposition::CMemoryLoadable {
            memory: snapshot,
            base,
            bytes,
            ..
        } = rewritten.proposition()
        else {
            panic!("viewability changed kind")
        };
        assert_eq!(snapshot.diagnostic_identity(), memory.diagnostic_identity());
        assert_eq!(base.block, PointerBlock::ExternalArgument);
        assert_eq!(
            base.offset,
            PointerOffsetTerm::add(target.clone(), PointerOffsetTerm::Constant(2))
        );
        assert_eq!(bytes, &extent);
        costs.push(work);
    }
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}

#[test]
fn pointer_view_rewrite_preserves_snapshot_extent_and_ambient_scaling() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = Pointer::symbolic(Variable(192_910));
    let target = Pointer::symbolic(Variable(192_911));
    let cited = Proposition::ConditionIs(
        ConditionTerm::pointer_equal(source.clone(), target.clone()),
        true,
    );
    let memory = CMemory::new().with_block("pointer-view-rewrite", 8);
    let extent = Bitvector32Term::Variable(Variable(192_912));
    let goal = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: source,
        bytes: extent.clone(),
        wide: false,
    };
    assert!(
        ProofFacts::default()
            .check_equality_rewrite(&goal, &cited)
            .is_err()
    );
    let mut costs = Vec::new();
    for size in [0, 4, 16, 64, 256] {
        let mut facts = ProofFacts::from_ordered(std::slice::from_ref(&cited));
        for index in 0..size {
            facts = facts.with_fact(equality(
                Bitvector32Term::Variable(Variable(200_000 + index)),
                Bitvector32Term::Constant(index as u32),
            ));
        }
        let (rewritten, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.check_equality_rewrite(&goal, &cited).unwrap()
        });
        let Proposition::CMemoryLoadable {
            memory: snapshot,
            base,
            bytes,
            wide: false,
        } = rewritten.proposition()
        else {
            panic!("viewability changed kind")
        };
        assert_eq!(snapshot.diagnostic_identity(), memory.diagnostic_identity());
        assert_eq!(base, &target);
        assert_eq!(bytes, &extent);
        costs.push(work);
    }
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}

#[test]
fn pointer_rewrite_enters_scalar_calls_and_preserves_scope_and_snapshots() {
    let variable = Variable(920);
    let source = Pointer::symbolic(variable);
    let target = Pointer::symbolic(Variable(921));
    let cited = Proposition::ConditionIs(
        ConditionTerm::PointerValueEqual(
            Box::new(CPointerValue::new(source.clone(), CType::Int32Pointer)),
            Box::new(CPointerValue::new(target.clone(), CType::Int32Pointer)),
        ),
        true,
    );
    let memory = CMemory::new().with_block("unchanged", 4);
    let goal_at = |pointer: Pointer, count: usize| {
        equality(
            Bitvector32Term::ClickFunctionApplication {
                name: "observes".into(),
                arguments: vec![
                    PureFunctionArgument::ArrayRef {
                        memory: memory.clone(),
                        pointer: CValue::typed_pointer(pointer, CType::Int32Pointer),
                        element_type: CType::Int32,
                    };
                    count
                ],
            },
            Bitvector32Term::Constant(1),
        )
    };
    let facts = ProofFacts::from_ordered(std::slice::from_ref(&cited));
    let goal = goal_at(source.clone(), 1);
    assert_eq!(
        facts
            .check_equality_rewrite(&goal, &cited)
            .unwrap()
            .proposition(),
        &goal_at(target.clone(), 1)
    );
    assert!(
        ProofFacts::default()
            .check_equality_rewrite(&goal, &cited)
            .is_err()
    );
    for bound in [variable, Variable(921)] {
        let quantified = Proposition::ForAll { name: Default::default(),
            var: bound,
            sort: Sort::CPointer(CType::Int32Pointer),
            body: Box::new(goal.clone()),
        };
        assert!(
            facts.check_equality_rewrite(&quantified, &cited).is_err(),
            "the equality cannot rewrite a shadowed source or capture the target"
        );
    }
    let displaced = Proposition::ConditionIs(
        ConditionTerm::pointer_equal(
            Pointer {
                block: source.block.clone(),
                offset: PointerOffsetTerm::Constant(4),
            },
            target.clone(),
        ),
        true,
    );
    assert!(
        ProofFacts::from_ordered(std::slice::from_ref(&displaced))
            .check_equality_rewrite(&goal, &displaced)
            .is_err(),
        "equality at an offset does not identify the whole pointer"
    );
    let costs = [16, 32, 64, 128].map(|size| {
        let goal = goal_at(source.clone(), size);
        let (checked, cost) = crate::instrumentation::measure_deterministic_work(|| {
            facts.check_equality_rewrite(&goal, &cited).unwrap()
        });
        assert_eq!(checked.proposition(), &goal_at(target.clone(), size));
        cost
    });
    assert!(costs[0] > 0);
    assert!(
        costs.windows(2).all(|pair| pair[1] <= 2 * pair[0] + 8),
        "scalar-call rewrite rescanned its argument list: {costs:?}"
    );
}

#[test]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn checked_rewrite_does_not_scan_or_rebuild_ambient_facts() {
    let x = Bitvector32Term::Variable(Variable(921));
    let cited = equality(x.clone(), Bitvector32Term::Constant(7));
    let goal = equality(x, Bitvector32Term::Constant(9));
    let mut costs = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut facts = ProofFacts::default();
        for index in 0..size {
            facts = facts.with_fact(equality(
                Bitvector32Term::Variable(Variable(10_000 + index)),
                Bitvector32Term::Constant(index as u32),
            ));
        }
        facts = facts.with_fact(cited.clone());
        super::super::super::take_fact_entry_counts();
        let (_, cost) = crate::instrumentation::measure_deterministic_work(|| {
            facts.check_equality_rewrite(&goal, &cited).unwrap()
        });
        assert_eq!(super::super::super::take_fact_entry_counts(), (0, 0));
        costs.push(cost);
    }
    assert!(costs[0] > 0);
    assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
}

#[test]
fn rewrite_capture_collection_does_not_visit_snapshot_contents() {
    let free = Variable(41);
    let address = Variable(42);
    let mut costs = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut memory = CMemory::new();
        for i in 0..size {
            memory = memory.store(
                Pointer::symbolic(Variable(100_000 + i)),
                CValue::Int32(Bitvector32Term::Variable(Variable(200_000 + i))),
            );
        }
        let equality = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(free)),
                Box::new(Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(memory),
                    Box::new(Pointer::symbolic(address)),
                    crate::kernel::LoadKind::Bits32,
                )),
            ),
            true,
        );
        let (variables, work) = crate::instrumentation::measure_deterministic_work(|| {
            rewrite_equality_variables(&equality).unwrap()
        });
        assert_eq!(variables, BTreeSet::from([free, address]));
        costs.push(work);
    }
    assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
}

#[test]
fn rewrite_integer_application_endpoint_keeps_byte_snapshot_and_ignores_its_contents() {
    let index = Bitvector32Term::Variable(Variable(47));
    let replacement = Bitvector32Term::Constant(9);
    let equality = Proposition::ConditionIs(
        ConditionTerm::equal(index.clone(), replacement.clone()),
        true,
    );
    let mut costs = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut memory = CMemory::new();
        for i in 0..size {
            memory = memory.store(
                Pointer::symbolic(Variable(300000 + i)),
                CValue::Int32(Bitvector32Term::Constant(i as u32)),
            );
        }
        let array = PureFunctionArgument::ArrayRef {
            memory,
            pointer: CValue::typed_pointer(Pointer::symbolic(Variable(48)), CType::UInt8Pointer),
            element_type: CType::UInt8,
        };
        let application = |endpoint| {
            IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                "prefix".into(),
                vec![
                    array.clone(),
                    PureFunctionArgument::Value(CValue::Int32(endpoint)),
                ],
            ))
        };
        let goal = Proposition::ConditionIs(
            ConditionTerm::integer_equal(
                application(index.clone()),
                application(replacement.clone()),
            ),
            true,
        );
        let expected = Proposition::ConditionIs(
            ConditionTerm::integer_equal(
                application(replacement.clone()),
                application(replacement.clone()),
            ),
            true,
        );
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&equality));
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts
                .check_equality_rewrite(&goal, &equality)
                .map(|checked| checked.proposition().clone())
        });
        assert_eq!(result.unwrap(), expected);
        costs.push(work);
    }
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work == costs[0]),
        "{costs:?}"
    );
}

#[test]
fn checked_integer_rewrite_is_exact_and_ignores_unrelated_facts() {
    let x: SharedIntegerTerm = IntegerTerm::var(Variable(187_001)).into();
    let y: SharedIntegerTerm = IntegerTerm::var(Variable(187_002)).into();
    let eq = |a, b| Proposition::ConditionIs(ConditionTerm::IntegerEqual(a, b), true);
    let cited = eq(x.clone(), y.clone());
    let goal = eq(
        IntegerTerm::TruncatingQuotient(x.clone(), IntegerTerm::constant_i64(2).into()).into(),
        y.clone(),
    );
    let expected = eq(
        IntegerTerm::TruncatingQuotient(y.clone(), IntegerTerm::constant_i64(2).into()).into(),
        y.clone(),
    );
    assert!(
        ProofFacts::default()
            .check_equality_rewrite(&goal, &cited)
            .is_err()
    );
    let mut costs = Vec::new();
    for size in [4u64, 16, 64, 256] {
        let mut facts = ProofFacts::default();
        for index in 0..size {
            facts = facts.with_fact(eq(
                IntegerTerm::var(Variable(188_000 + index)).into(),
                IntegerTerm::constant_i64(index as i64).into(),
            ));
        }
        // Admission may use the reversed exact fact; rewriting follows the cited direction.
        facts = facts.with_fact(eq(y.clone(), x.clone()));
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.check_equality_rewrite(&goal, &cited)
        });
        assert_eq!(checked.unwrap().proposition(), &expected);
        costs.push(work);
        assert!(
            facts
                .check_equality_rewrite(&goal, &eq(x.clone(), IntegerTerm::constant_i64(42).into()))
                .is_err()
        );
    }
    assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
    let captured = Proposition::ForAll { name: Default::default(),
        var: Variable(187_001),
        sort: Sort::Integer,
        body: Box::new(goal.clone()),
    };
    assert!(
        ProofFacts::default()
            .with_fact(cited.clone())
            .check_equality_rewrite(&captured, &cited)
            .is_err()
    );
    let mut false_equality = cited.clone();
    if let Proposition::ConditionIs(_, truth) = &mut false_equality {
        *truth = false;
    }
    assert!(
        ProofFacts::default()
            .with_fact(false_equality.clone())
            .check_equality_rewrite(&goal, &false_equality)
            .is_err()
    );
}

#[test]
fn integer_observation_rewrite_work_tracks_selected_comparison_leaves() {
    let word = Bitvector32Term::Variable(Variable(74_201));
    let source: SharedIntegerTerm =
        IntegerTerm::from_machine(MachineIntegerType::UInt64, word.clone())
            .unwrap()
            .into();
    let target: SharedIntegerTerm = IntegerTerm::var(Variable(74_202)).into();
    let cited = Proposition::ConditionIs(ConditionTerm::IntegerEqual(source, target.clone()), true);
    let leaf = Proposition::ConditionIs(
        observed_native_condition(
            MachineIntegerType::UInt64,
            1,
            word,
            observed_native_bound(MachineIntegerType::UInt64),
        ),
        true,
    );
    let samples = [8usize, 16, 32, 64].map(|size| {
        let mut goal = leaf.clone();
        for _ in 1..size {
            goal = Proposition::And(Box::new(goal), Box::new(leaf.clone()));
        }
        let (rewritten, work) = crate::instrumentation::measure_deterministic_work(|| {
            rewrite_with_admitted_equality(&goal, &cited).unwrap()
        });
        let mut pending = vec![&rewritten];
        let mut leaves = 0;
        while let Some(proposition) = pending.pop() {
            match proposition {
                Proposition::And(left, right) => {
                    pending.push(left);
                    pending.push(right);
                }
                Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(left, right), true) => {
                    assert_eq!(left, &target);
                    assert_eq!(right.as_ref(), &IntegerTerm::constant_i64(10));
                    leaves += 1;
                }
                _ => panic!("a selected native comparison lost its observed rewrite"),
            }
        }
        assert_eq!(leaves, size);
        assert!(work <= 128 * size + 256, "{size}: {work} work");
        work
    });
    for pair in samples.windows(2) {
        assert!(
            pair[1] > pair[0] && pair[1] <= 2 * pair[0] + 32,
            "{samples:?}"
        );
    }
}
