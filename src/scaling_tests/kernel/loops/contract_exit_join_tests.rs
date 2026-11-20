// Scaling tests of `src/kernel/loops.rs` (module `contract_exit_join_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn loop_exit_scalar_restatement_keeps_recorded_memory_effects() {
    let _session = crate::kernel::VerificationSession::enter();
    let held = int32(MachineTerm::Variable(Variable(927_020)));
    let fresh = int32(MachineTerm::Variable(Variable(927_021)));
    let guard = |value| {
        program_value_comparison_proposition(value, ComparisonOperator::Equal, &int32(3)).unwrap()
    };
    let range = MemoryRange::new_with_element_width(
        Address::symbolic(Variable(927_022)),
        MachineTerm::constant(0),
        MachineTerm::Variable(Variable(927_020)),
        4,
    );
    let slot = SymbolicMemory::local_pointer("counter");
    let work = [4u32, 16, 64, 256].map(|size| {
        let mut before = SymbolicMemory::new().with_block(slot.base.clone(), 4);
        for index in 0..size {
            before = before.with_block(format!("untouched{index}").as_str(), 4);
        }
        let after = before.clone().store(slot.clone(), held.clone());
        let effect = Proposition::MemoryEffectSummary {
            before,
            after,
            mutable_ranges: vec![range.clone()],
        };
        let original = Proposition::And(Box::new(effect.clone()), Box::new(guard(&held)));
        let facts = [
            ExecutionPureFact::new(effect.clone()),
            ExecutionPureFact::new(original.clone()),
        ]
        .into_iter()
        .collect();
        let mut restatement = LoopExitRestatement::default();
        restatement.pin(&fresh, &held);
        let (exit, work) = crate::instrumentation::measure_deterministic_work(|| {
            restatement.restate(facts, vec![], empty_checked_loan_evidence_sequence())
        });
        assert!(exit.stated.contains_proposition(&original));
        let nested = Proposition::And(Box::new(effect.clone()), Box::new(guard(&fresh)));
        assert_eq!(exit.disjunct, [effect, nested]);
        assert!(exit.successor_equations.is_empty());
        work
    });
    assert!(
        work.iter().all(|units| *units == work[0]),
        "loop exit restatement work with 4/16/64/256 untouched blocks: {work:?}"
    );
}

#[test]
fn a_loop_exit_join_visits_only_changed_bindings_and_cells() {
    let _session = crate::kernel::VerificationSession::enter();
    let left_only = SymbolicMemory::global_pointer("left-exit-only");
    let right_only = SymbolicMemory::global_pointer("exit-only");
    let work = [4u32, 16, 64, 256].map(|size| {
        let mut shared = ExecutionState::new()
            .with_local("counter", int32(0))
            .with_local("maybe_initialized", int32(7));
        let mut memory = SymbolicMemory::new().with_block("shared", 4 * size);
        for index in 0..size {
            shared = shared.with_local(format!("spare{index}"), int32(index));
            let pointer = Address {
                base: AddressBase::from("shared"),
                offset: AddressOffset::Constant(i64::from(index) * 4),
            };
            memory = memory.store(pointer, int32(index));
        }
        let shared = shared.with_memory(memory.clone());
        let left = shared
            .clone()
            .with_local("counter", int32(1))
            .with_memory(memory.clone().store(left_only.clone(), int32(11)));
        let mut right = shared
            .clone()
            .with_local("counter", int32(2))
            .with_memory(memory.clone().store(right_only.clone(), int32(12)));
        assert!(right.locals.forget_initialization("maybe_initialized"));
        let head = LoopHead {
            top: shared.clone(),
            body: shared.clone(),
            guard: shared.clone(),
            entry: shared,
            iterations: IntegerTerm::Constant(0.into()),
            summaries: Vec::new(),
            resource_failures: Vec::new(),
            loan_requirements: Vec::new(),
            effect_checks: Vec::new(),
        };
        let facts = ExecutionFacts::new();
        let mut requirements = Vec::new();
        let ((joined, restatements), work) =
            crate::instrumentation::measure_deterministic_work(|| {
                abstract_loop_exit_states(
                    &head,
                    &ProgramStatement::Skip,
                    &[],
                    &[&left, &right],
                    &[&facts, &facts],
                    &[],
                    &PureFactContext::new(),
                    &mut requirements,
                    &mut KernelVariableGenerator::fresh_for_execution(BTreeSet::new()),
                    &mut ExecutionBudget::default(),
                )
                .unwrap()
            });
        assert!(joined.locals.is_uninitialized_object("maybe_initialized"));
        assert_eq!(
            joined.locals.get("spare0").unwrap().native().as_ref(),
            &int32(0)
        );
        assert_eq!(joined.memory().cells, memory.cells);
        assert!(requirements.is_empty());
        assert_eq!(restatements.len(), 2);
        assert!(restatements.iter().all(|exit| exit.equations.len() == 1));

        // A later exit may hold a cache entry the successor never had.
        // Also measure selection on its own when only the later exit has a
        // cell to set aside.
        let exits = [
            joined.clone(),
            joined
                .clone()
                .with_memory(memory.store(right_only.clone(), int32(12))),
        ];
        let mut successor = joined;
        let (cells, cell_work) = crate::instrumentation::measure_deterministic_work(|| {
            abstract_loop_exit_memory(
                &mut successor,
                &exits,
                &BTreeSet::new(),
                true,
                &[],
                &PureFactContext::new(),
                &[],
                &mut [
                    LoopExitRestatement::default(),
                    LoopExitRestatement::default(),
                ],
                &mut requirements,
                &mut KernelVariableGenerator::fresh_for_execution(BTreeSet::new()),
                &mut ExecutionBudget::default(),
            )
            .unwrap()
        });
        assert_eq!(cells, BTreeSet::from([right_only.clone()]));
        assert!(successor.memory().known_value(&right_only).is_none());
        assert!(requirements.is_empty());
        (work, cell_work)
    });
    eprintln!(
        "(exit join, cell selection) work at 4/16/64/256 shared bindings and cells: {work:?}"
    );
    assert!(
        work.iter().all(|&(join, cells)| {
            join > 0 && cells > 0 && join <= work[0].0 + 64 && cells <= work[0].1 + 16
        }),
        "(exit join, cell selection) work at 4/16/64/256 shared bindings and cells: {work:?}"
    );
}

#[test]
fn exit_cell_separation_shares_the_active_loan_footprint() {
    use crate::kernel::loans::BorrowLedger;

    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Address::symbolic(Variable(927_000));
    let range = |base| MemoryRange::new_with_element_width(base, 0u32.into(), 4u32.into(), 1);
    let expected_left = Box::new(Resource::Memory(range(pointer.clone())));
    let memory = SymbolicMemory::new().with_block(pointer.base.clone(), 4);
    let mut samples = Vec::new();
    for count in [4u64, 16, 64, 256] {
        let mut ledger = BorrowLedger::new();
        let holder = ledger.fresh_participant().unwrap();
        for index in 0..count {
            // Include overlap with the changed cell. Construction must retain
            // the prerequisite even here, without trying to prove it.
            let view =
                ResourceFact::view_memory(range(Address::symbolic(Variable(927_000 + index))));
            let (_, occurrences) =
                ResourceContext::new().unchecked_with_facts_and_occurrences([view.clone()]);
            let opening = ledger
                .borrowed_contract_input(holder, occurrences[0].1, view, None)
                .unwrap();
            ledger = ledger.apply(&opening.transition).unwrap();
        }
        let base = ExecutionState::new()
            .with_memory(memory.clone())
            .with_loan_ledger(Some(ledger.clone()));
        let exits = [
            base.clone()
                .with_memory(memory.clone().store(pointer.clone(), int32(0))),
            base,
        ];
        let mut successor = exits[0].clone();
        let mut requirements = Vec::new();
        let (cells, work) = crate::instrumentation::measure_deterministic_work(|| {
            abstract_loop_exit_memory(
                &mut successor,
                &exits,
                &BTreeSet::new(),
                true,
                &[],
                &PureFactContext::new(),
                &[],
                &mut [
                    LoopExitRestatement::default(),
                    LoopExitRestatement::default(),
                ],
                &mut requirements,
                &mut KernelVariableGenerator::fresh_for_execution(BTreeSet::new()),
                &mut ExecutionBudget::default(),
            )
            .unwrap()
        });
        assert_eq!(cells, BTreeSet::from([pointer.clone()]));
        assert!(successor.memory().known_value(&pointer).is_none());
        let [requirement] = requirements.as_slice() else {
            panic!("expected one separation condition for the dropped cell");
        };
        assert!(!requirement.is_assumable());
        assert!(requirement.requires_statement_entry());
        let expected = ledger
            .memory_access_requirement(&range(pointer.clone()))
            .unwrap();
        assert_eq!(requirement.proposition(), &expected);
        assert!(matches!(
            requirement.proposition(),
            Proposition::ResourceSeparate { left, .. } if left == &expected_left
        ));
        samples.push(work);
    }
    assert!(
        samples[0] > 0 && samples.iter().all(|work| *work <= samples[0] + 16),
        "{samples:?}"
    );
}

#[test]
fn contract_exit_marker_join_work_is_linear_in_exits_and_skips_ambient_cells() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut samples = Vec::new();
    for count in [4usize, 64, 1024] {
        let exits = marker_exits(count, 4);
        let (successor, work) = measured_join(&exits);
        samples.push((count, work));
        assert!(work > 0 && work <= count * 30 + 32, "{samples:?}");
        assert_eq!(successor.memory.cells, exits[0].memory.cells);
        assert_eq!(
            crate::kernel::reasoning::memory_resolution::havoc_marker_blocks(
                &successor.memory.blocks
            )
            .count(),
            2
        );
    }
    eprintln!("(exits, marker join work): {samples:?}");
    let mut ambient_work = Vec::new();
    for ambient in [4usize, 64, 1024] {
        let (_, work) = measured_join(&marker_exits(4, ambient));
        ambient_work.push(work);
    }
    assert!(
        ambient_work.iter().all(|work| *work <= ambient_work[0] * 2),
        "{ambient_work:?}"
    );
}

#[test]
fn optional_exit_cache_reconciliation_does_not_walk_unrelated_store_history() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Address {
        base: "shared".into(),
        offset: AddressOffset::Constant(0),
    };
    let other = Address {
        base: "other".into(),
        offset: AddressOffset::Constant(0),
    };
    let mut samples = Vec::new();
    for count in [4usize, 64, 1024] {
        let mut memory = SymbolicMemory::new()
            .with_block("shared", 4)
            .with_block("other", 4);
        for index in 0..count {
            memory = memory.store(other.clone(), int32(index as u32));
        }
        let mut exits = [
            ExecutionState::new().with_memory(memory.clone().store(pointer.clone(), int32(0))),
            ExecutionState::new().with_memory(memory),
        ];
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            retain_proven_loop_exit_cells(
                &mut exits,
                &[&ExecutionFacts::new(), &ExecutionFacts::new()],
                &[],
                &PureFactContext::new(),
                true,
            )
        });
        result.unwrap();
        assert!(exits[1].memory().known_value(&pointer).is_none());
        samples.push(work);
    }
    assert!(
        samples[0] > 0 && samples.iter().all(|work| *work <= samples[0] * 2),
        "{samples:?}"
    );
    eprintln!("optional cache lookup work at 4/64/1024 old stores: {samples:?}");
}

/// The exit join indexes each exit's facts once. Cache reconciliation reads
/// the contexts the join already built for its binders instead of assuming
/// the same exit facts a second time, so with them it rebuilds no context
/// entries however many facts an exit carries. Rebuilding them cost the
/// `flips_red_all` loop's exit join about 134,000 control units.
#[test]
fn exit_cache_reconciliation_reuses_the_joins_exit_contexts() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Address {
        base: AddressBase::Concrete("shared".into()),
        offset: AddressOffset::Constant(0),
    };
    let memory = SymbolicMemory::new().with_block("shared", 4);
    // Name the cell's load, as the exit's own read did.
    let load = symbolic_storage_cell_value(&memory, &pointer, ProgramType::Int32, true).unwrap();
    let zero = int32(0);
    let exits = || {
        [
            ExecutionState::new().with_memory(memory.clone().store(pointer.clone(), zero.clone())),
            ExecutionState::new().with_memory(memory.clone()),
        ]
    };
    let mut rebuilt = Vec::new();
    let mut reused = Vec::new();
    for count in [4usize, 16, 64, 256] {
        let mut facts = (0..count)
            .map(|k| {
                ExecutionPureFact::new(Proposition::condition_is(
                    ConditionTerm::signed_less_than(
                        MachineTerm::Variable(Variable(926_000 + k as u64)),
                        MachineTerm::constant(k as u32),
                    ),
                    true,
                ))
            })
            .collect::<Vec<_>>();
        facts.push(ExecutionPureFact::new(
            program_value_comparison_proposition(&load, ComparisonOperator::Equal, &zero).unwrap(),
        ));
        let exit_facts = ExecutionFacts::from(facts);
        let empty = ExecutionFacts::new();
        let all = [&empty, &exit_facts];

        let mut states = exits();
        let before = crate::kernel::reasoning::path_facts::context_rebuild_entries();
        retain_proven_loop_exit_cells(&mut states, &all, &[], &PureFactContext::new(), true)
            .unwrap();
        rebuilt.push(crate::kernel::reasoning::path_facts::context_rebuild_entries() - before);
        assert_eq!(states[1].memory().known_value(&pointer), Some(zero.clone()));

        let built = loop_exit_argument_contexts(&all, &[], &PureFactContext::new(), true);
        let mut states = exits();
        let before = crate::kernel::reasoning::path_facts::context_rebuild_entries();
        retain_proven_loop_exit_cells(&mut states, &all, &built, &PureFactContext::new(), true)
            .unwrap();
        reused.push(crate::kernel::reasoning::path_facts::context_rebuild_entries() - before);
        assert_eq!(states[1].memory().known_value(&pointer), Some(zero.clone()));
    }
    assert!(
        rebuilt
            .iter()
            .zip([4usize, 16, 64, 256])
            .all(|(entries, count)| *entries > count),
        "without the join's contexts an exit's facts are assumed here: {rebuilt:?}"
    );
    assert!(
        reused.iter().all(|entries| *entries == 0),
        "reconciliation assumed exit facts the join already indexed: {reused:?}"
    );
}

#[test]
fn loop_exit_cell_pins_use_indexed_constants() {
    let _session = crate::kernel::VerificationSession::enter();
    let held = int32(MachineTerm::Variable(Variable(1)));
    let missing = int32(MachineTerm::Variable(Variable(2)));
    let equation = |left: &ProgramValue, right: &ProgramValue| {
        program_value_comparison_proposition(left, ComparisonOperator::Equal, right).unwrap()
    };
    let mut samples = Vec::new();
    for size in [4u32, 16, 64, 256] {
        let mut context = PureFactContext::new().assume_proposition(equation(&held, &int32(1)));
        for index in 0..size {
            context = context.assume_proposition(equation(
                &held,
                &int32(MachineTerm::Variable(Variable(100 + u64::from(index)))),
            ));
            context = context.assume_proposition(equation(
                &int32(MachineTerm::Variable(Variable(1000 + u64::from(index)))),
                &int32(7),
            ));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(loop_exit_cell_pin_value(&held, &context), int32(1));
            assert_eq!(loop_exit_cell_pin_value(&missing, &context), missing);
            assert_eq!(
                loop_exit_cell_pin_value(&held, &PureFactContext::new()),
                held
            );
        });
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] * 2 + 32),
        "{samples:?}"
    );
}

#[test]
fn loop_exit_integer_field_equations_retain_growing_roots() {
    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let base_root = KernelTerm::variable(KernelType::Integer, Variable(950_001));
        let mut held_root = base_root.clone();
        for _ in 0..size {
            held_root = KernelTerm::integer_operation(
                KernelIntegerOperator::Add,
                vec![held_root.clone(), held_root],
            )
            .unwrap();
        }
        let base =
            ResourceFieldValues::from_stored([StoredResourceField::Integer(base_root.clone())]);
        let other =
            ResourceFieldValues::from_stored([StoredResourceField::Integer(held_root.clone())]);
        let mut restatements = [
            LoopExitRestatement::default(),
            LoopExitRestatement::default(),
        ];
        let mut variables =
            KernelVariableGenerator::fresh_for_execution(BTreeSet::from([Variable(950_001)]));
        let mut budget = ExecutionBudget::new();
        let (joined, work) = crate::instrumentation::measure_deterministic_work(|| {
            joined_resource_fields(
                &base,
                [&base, &other].into_iter(),
                &mut restatements,
                &mut variables,
                &mut budget,
            )
            .unwrap()
        });
        let joined = joined.retained_integer(0).unwrap();
        assert_ne!(joined, &base_root);
        for (restatement, expected) in restatements.iter().zip([&base_root, &held_root]) {
            let [Proposition::Equal(Term::Integer(fresh), Term::Integer(held))] =
                restatement.equations.as_slice()
            else {
                panic!("one Integer field equation per exit")
            };
            assert_eq!(fresh.root(), Some(joined));
            assert_eq!(held.root(), Some(expected));
        }
        assert!(!base_root.has_cached_native_argument());
        assert!(!held_root.has_cached_native_argument());
        assert!(work < 128, "size={size} work={work}");
    }
}
