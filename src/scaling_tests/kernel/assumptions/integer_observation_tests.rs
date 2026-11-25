// Scaling tests of native fact queries through exact Integer observations.

#[test]
fn native_observation_queries_use_the_selected_fact_index() {
    let samples = [8u64, 32, 128, 512].map(|size| {
        let condition = OldConditionTerm::IntegerEqual(
            observe(MachineIntegerType::Int32, 880_001),
            constant(0),
        );
        let (native, truth) = native_comparison_of_integer_observation(&condition, false).unwrap();
        let mut context = PureFactContext::new().assume_condition(native, truth);
        for index in 0..size {
            context = context.assume_condition(
                OldConditionTerm::equal(word(890_000 + index), OldMachineTerm::constant(7)),
                true,
            );
        }
        let (known, work) = crate::persistent::measure_persistent_work(|| {
            context.contains_known(&Proposition::condition_is(condition, false))
        });
        assert!(known);
        work
    });
    assert!(samples[0] > 0);
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 2 * pair[0] + 32),
        "an observation query scanned unrelated facts: {samples:?}"
    );
}

#[test]
fn filing_an_integer_reading_through_an_operation_visits_only_its_own_bounds() {
    // Filing the Integer reading of a native guard, and the second bound of
    // a signed definedness fact, looks up only those facts' own bounds,
    // however many unrelated facts the context holds.
    let samples = [8u64, 32, 128, 512].map(|size| {
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(
                OldConditionTerm::IntegerLessEqual(
                    difference(900_000 + index, 900_001 + index),
                    constant(7),
                ),
                true,
            );
        }
        let guard = OldConditionTerm::IntegerLessEqual(
            observe(MachineIntegerType::UInt32, 1),
            uint32_difference_from(4_294_967_295, 2),
        );
        let upper = OldConditionTerm::IntegerLessEqual(difference(3, 4), constant(2_147_483_647));
        let lower =
            OldConditionTerm::IntegerGreaterEqual(difference(3, 4), constant(-2_147_483_648));
        let context = context.assume_condition(upper, true);
        let (context, work) = crate::persistent::measure_persistent_work(|| {
            context
                .assume_condition(guard, true)
                .assume_condition(lower, true)
        });
        assert_eq!(context.decide(&uint32_guard(u32::MAX, 1, 2)), Some(true));
        assert_eq!(
            context.decide(&OldConditionTerm::signed_subtract_overflows(
                word(3),
                word(4)
            )),
            Some(false)
        );
        work
    });
    assert!(samples[0] > 0);
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 2 * pair[0] + 32),
        "filing an operation reading scanned unrelated facts: {samples:?}"
    );
}

#[test]
fn filing_a_quantified_integer_antecedent_visits_only_its_own_bounds() {
    // Filing a quantified fact whose antecedent reads through an in-range
    // sum looks up only that sum's range bound, however many unrelated facts
    // the context holds.
    let samples = [8u64, 32, 128, 512].map(|size| {
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(
                OldConditionTerm::IntegerLessEqual(
                    difference(900_000 + index, 900_001 + index),
                    constant(7),
                ),
                true,
            );
        }
        let sum: SharedIntegerTerm =
            IntegerTerm::Add(observe(MachineIntegerType::UInt64, 831), constant(1)).into();
        let reading = OldConditionTerm::IntegerLessThan(
            observe(MachineIntegerType::UInt64, 830),
            sum.clone(),
        );
        let (native, truth, _) =
            native_comparison_through_integer_operations(&reading, true).unwrap();
        let context =
            context.assume_condition(OldConditionTerm::IntegerLessEqual(sum, uint64_max()), true);
        let (context, work) = crate::persistent::measure_persistent_work(|| {
            context.assume_proposition(quantified_over_k(Proposition::condition_is(reading, true)))
        });
        assert!(
            context.contains_known(&quantified_over_k(Proposition::condition_is(native, truth)))
        );
        work
    });
    assert!(samples[0] > 0);
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 2 * pair[0] + 32),
        "filing a quantified antecedent's reading scanned unrelated facts: {samples:?}"
    );
}

#[test]
fn admitting_modular_equalities_does_not_export_shared_operands() {
    use crate::kernel::{KernelTerm, KernelType, MachineBinaryOp, SharedMachineIntegerTerm};
    let mut samples = Vec::new();
    for size in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut root =
            KernelTerm::variable(KernelType::Program(format.program_type()), Variable(982705));
        let mut context = PureFactContext::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for step in 0..size {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [root.clone(), root.clone()],
                );
                let machine = SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap();
                let exact = IntegerTerm::Add(
                    IntegerTerm::Machine(machine.clone()).into(),
                    IntegerTerm::constant(1.into()).into(),
                );
                context = context.clone().assume_condition(
                    OldConditionTerm::IntegerEqual(
                        exact.into(),
                        IntegerTerm::from_machine(
                            format,
                            crate::kernel::OldMachineTerm::Variable(Variable(983000 + step as u64)),
                        )
                        .unwrap()
                        .into(),
                    ),
                    true,
                );
                assert!(!machine.has_boxed_operand());
            }
        });
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small * 4 <= sw * large * 5, "{samples:?}");
    }
}

#[test]
fn inverse_operation_mapping_retains_shared_prefixes() {
    use crate::kernel::machine_integer::identity::machine_operation_of_integer_value;
    use crate::kernel::{KernelTerm, KernelType, MachineBinaryOp, SharedMachineIntegerTerm};
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        for unrelated in [0, 128] {
            let _unrelated = (0..unrelated)
                .map(|i| KernelTerm::variable(KernelType::Integer, Variable(984000 + i)))
                .collect::<Vec<_>>();
            let mut samples = Vec::new();
            for size in [8, 32, 96] {
                let _session = crate::kernel::VerificationSession::enter();
                let mut root = KernelTerm::variable(
                    KernelType::Program(format.program_type()),
                    Variable(982801),
                );
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    for _ in 0..size {
                        root = KernelTerm::machine_binary_shared(
                            format,
                            MachineBinaryOp::Add,
                            [root.clone(), root.clone()],
                        );
                        let machine =
                            SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap();
                        let observation = IntegerTerm::Machine(machine.clone());
                        for exact in [
                            IntegerTerm::Add(
                                observation.clone().into(),
                                IntegerTerm::constant(1.into()).into(),
                            ),
                            IntegerTerm::Subtract(
                                observation.clone().into(),
                                observation.clone().into(),
                            ),
                        ] {
                            let (result, _) =
                                machine_operation_of_integer_value(&exact, format).unwrap();
                            let IntegerTerm::Machine(result) = result else {
                                panic!("operation observation")
                            };
                            assert!(!machine.has_boxed_operand());
                            assert!(!result.has_boxed_operand());
                        }
                        let multiply =
                            IntegerTerm::Multiply(observation.clone().into(), observation.into());
                        assert!(machine_operation_of_integer_value(&multiply, format).is_none());
                        assert!(!machine.has_boxed_operand());
                    }
                });
                samples.push((size, work));
            }
            for pair in samples.windows(2) {
                let [(small, sw), (large, lw)] = pair else {
                    unreachable!()
                };
                assert!(lw * small * 4 <= sw * large * 5, "{samples:?}");
            }
        }
    }
}

fn ordinary_comparison_admission_retains_shared_operands(ty: MachineIntegerType) {
    use crate::kernel::{KernelTerm, KernelType, MachineBinaryOp, SharedMachineIntegerTerm};
    for size in [8, 32, 96] {
        for equality in [false, true] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut root = KernelTerm::variable(
                KernelType::Program(ty.program_type()),
                Variable(991800 + u64::from(equality)),
            );
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [root.clone(), root.clone()],
                );
            }
            let operand = SharedMachineIntegerTerm::from_shared(ty, root).unwrap();
            let observed = IntegerTerm::Machine(operand.clone()).into();
            let constant = IntegerTerm::constant(100.into()).into();
            let condition = if equality {
                OldConditionTerm::IntegerEqual(observed, constant)
            } else {
                OldConditionTerm::IntegerLessEqual(observed, constant)
            };
            let source = Proposition::condition_is(condition, true);
            let facts = PureFactContext::new().assume_proposition(source.clone());
            assert!(
                !operand.has_boxed_operand(),
                "size={size}, equality={equality}"
            );
            assert!(facts.contains_assumed_exact(&source));
        }
    }
}

#[test]
fn ordinary_comparison_admission_retains_shared_int8() {
    ordinary_comparison_admission_retains_shared_operands(MachineIntegerType::Int8);
}

#[test]
fn ordinary_comparison_admission_retains_shared_uint8() {
    ordinary_comparison_admission_retains_shared_operands(MachineIntegerType::UInt8);
}

#[test]
fn ordinary_comparison_admission_retains_shared_int16() {
    ordinary_comparison_admission_retains_shared_operands(MachineIntegerType::Int16);
}

#[test]
fn ordinary_comparison_admission_retains_shared_uint16() {
    ordinary_comparison_admission_retains_shared_operands(MachineIntegerType::UInt16);
}

#[test]
fn ordinary_comparison_admission_retains_shared_int32() {
    ordinary_comparison_admission_retains_shared_operands(MachineIntegerType::Int32);
}

#[test]
fn ordinary_comparison_admission_retains_shared_uint32() {
    ordinary_comparison_admission_retains_shared_operands(MachineIntegerType::UInt32);
}

#[test]
fn ordinary_comparison_admission_retains_shared_int64() {
    ordinary_comparison_admission_retains_shared_operands(MachineIntegerType::Int64);
}

#[test]
fn ordinary_comparison_admission_retains_shared_uint64() {
    ordinary_comparison_admission_retains_shared_operands(MachineIntegerType::UInt64);
}

#[test]
fn observation_alias_source_lookup_does_not_scan_supports() {
    for related in [false, true] {
        let samples = [8u64, 32, 128, 512].map(|size| {
            let _session = crate::kernel::VerificationSession::enter();
            let mut index = observation_comparisons::ObservationComparisons::default();
            for n in 0..size {
                let variable = if related { 991900 } else { 991900 + n };
                let bound = IntegerTerm::Add(constant(n as i64), constant(100 - n as i64)).into();
                index.adjust(
                    &OldConditionTerm::IntegerLessEqual(
                        observe(MachineIntegerType::UInt32, variable),
                        bound,
                    ),
                    true,
                );
            }
            let hit =
                OldConditionTerm::unsigned_less_equal(word(991900), OldMachineTerm::constant(100));
            let miss =
                OldConditionTerm::unsigned_less_equal(word(991900), OldMachineTerm::constant(101));
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                assert!(index.source(&hit, true).is_some());
                assert!(index.source(&miss, true).is_none());
                assert!(index.source(&hit, false).is_none());
            });
            work
        });
        assert!(samples[0] > 0);
        assert!(
            samples.windows(2).all(|p| p[1] <= 2 * p[0] + 32),
            "related={related}: {samples:?}"
        );
    }
}

#[test]
fn shared_contradiction_admission_updates_only_new_additive_structure() {
    use crate::kernel::{KernelTerm, KernelType, MachineBinaryOp, SharedMachineIntegerTerm};
    let samples = [8, 32, 96].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let mut root =
            KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(993000));
        let mut facts = contradictions::ContextContradictions::default();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for n in 0..size {
                let fresh = KernelTerm::variable(
                    KernelType::Program(ty.program_type()),
                    Variable(993001 + n),
                );
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [root.clone(), fresh],
                );
                let operand = SharedMachineIntegerTerm::from_shared(ty, root.clone()).unwrap();
                facts.adjust(
                    &OldConditionTerm::IntegerLessEqual(
                        IntegerTerm::Machine(operand.clone()).into(),
                        constant(100),
                    ),
                    true,
                );
                assert!(!operand.has_boxed_operand());
            }
        });
        (size as usize, work)
    });
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small * 2 <= sw * large * 3, "{samples:?}");
    }
}

#[test]
fn repeated_shared_comparison_admission_is_near_linear() {
    use crate::kernel::{KernelTerm, KernelType, MachineBinaryOp, SharedMachineIntegerTerm};
    let samples = [8usize, 32, 96].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let mut root =
            KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(994000));
        let mut facts = PureFactContext::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [root.clone(), root.clone()],
                );
                let operand = SharedMachineIntegerTerm::from_shared(ty, root.clone()).unwrap();
                facts = facts.clone().assume_condition(
                    OldConditionTerm::IntegerLessEqual(
                        IntegerTerm::Machine(operand.clone()).into(),
                        constant(100),
                    ),
                    true,
                );
                assert!(!operand.has_boxed_operand());
            }
        });
        (size, work)
    });
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small * 2 <= sw * large * 3, "{samples:?}");
    }
}

#[test]
fn operation_and_quantified_bridges_retain_shared_operands() {
    use crate::kernel::{KernelTerm, KernelType, MachineBinaryOp, SharedMachineIntegerTerm};
    for size in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::UInt64;
        let mut root =
            KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(994001));
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                ty,
                MachineBinaryOp::Add,
                [root.clone(), root.clone()],
            );
        }
        let operand = SharedMachineIntegerTerm::from_shared(ty, root).unwrap();
        let sum: SharedIntegerTerm =
            IntegerTerm::Add(IntegerTerm::Machine(operand.clone()).into(), constant(1)).into();
        let source = OldConditionTerm::IntegerLessThan(observe(ty, 830), sum.clone());
        let (view, _) =
            crate::kernel::machine_integer::comparison::comparison_view_through_integer_operations(
                &source, true,
            )
            .unwrap();
        let reading = view.integer_condition();
        let bounded = PureFactContext::new()
            .assume_condition(OldConditionTerm::IntegerLessEqual(sum, uint64_max()), true);
        let facts = bounded.clone().assume_condition(source.clone(), true);
        assert!(facts.contains_known(&Proposition::condition_is(reading.clone(), true)));
        let facts =
            bounded.assume_proposition(quantified_over_k(Proposition::condition_is(source, true)));
        assert!(facts.contains_known(&quantified_over_k(Proposition::condition_is(reading, true))));
        // Key both the original Integer source and its shared consequence.
        facts.build_stated_proposition_index();
        assert!(!operand.has_boxed_operand(), "size={size}");
    }
}

#[test]
fn constant_bound_selection_rejects_shared_symbolic_candidates_without_export() {
    use crate::kernel::{KernelTerm, KernelType, MachineBinaryOp, SharedMachineIntegerTerm};
    for ty in [MachineIntegerType::Int32, MachineIntegerType::Int64] {
        for size in [8, 32, 96] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut root =
                KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(994011));
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [root.clone(), root.clone()],
                );
            }
            let operand = SharedMachineIntegerTerm::from_shared(ty, root).unwrap();
            let source = OldConditionTerm::IntegerLessEqual(
                observe(ty, 994010),
                IntegerTerm::Machine(operand.clone()).into(),
            );
            let facts = PureFactContext::new().assume_condition(source, true);
            let width = if ty == MachineIntegerType::Int32 {
                SignedDefinedWidth::Int32
            } else {
                SignedDefinedWidth::Int64
            };
            assert!(
                facts
                    .signed_constant_bound_facts(width, &word(994010))
                    .is_empty()
            );
            assert!(!operand.has_boxed_operand(), "{ty:?}, size={size}");
        }
    }
}

#[test]
fn shared_bound_source_selection_uses_existing_index_across_branches() {
    use crate::kernel::machine_integer::comparison::condition_for_operand_views;
    use crate::kernel::{KernelTermExport, KernelTermImport, MachineOperandView};
    let samples = [16u64, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let term = OldMachineTerm::add(word(189141), word(189142));
        let zero = OldMachineTerm::constant(0);
        let source = Proposition::condition_is(
            OldConditionTerm::signed_less_equal(zero.clone(), term.clone()),
            true,
        );
        let root = KernelTermImport::default()
            .machine_arithmetic(MachineIntegerType::Int32, &term)
            .unwrap();
        let goal = condition_for_operand_views(
            MachineIntegerType::Int32,
            CompareRelation::LessEqual,
            [
                MachineOperandView::Old(&zero),
                MachineOperandView::Shared(&root),
            ],
        );
        let mut child = PureFactContext::new();
        for n in 0..size {
            child = child.assume_condition(
                OldConditionTerm::signed_less_equal(zero.clone(), word(189150 + n)),
                true,
            );
        }
        let parent = child.clone().assume_proposition(source.clone());
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                parent
                    .checked_order_bounds
                    .exact_observation_source(&goal, true),
                Some(source.clone())
            );
            assert_eq!(
                child
                    .checked_order_bounds
                    .exact_observation_source(&goal, true),
                None
            );
            assert_eq!(
                parent
                    .checked_order_bounds
                    .exact_observation_source(&goal, false),
                None
            );
            let (_, used) = collect_consulted_premises(|| {
                record_consulted_premises(&parent, &Proposition::condition_is(goal.clone(), true));
            });
            assert_eq!(used, vec![source.clone()]);
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work
    });
    assert!(samples[0] > 0);
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] * 2 + 32),
        "{samples:?}"
    );
}
