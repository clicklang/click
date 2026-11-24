use super::*;

#[test]
fn retained_integer_arithmetic_substitution_visits_shared_nodes_once_without_exports() {
    let _session = VerificationSession::enter();
    for size in [16, 64, 256] {
        let from = Variable(991950);
        let mut root = KernelTerm::variable(KernelType::Integer, from);
        for _ in 0..size {
            root =
                KernelTerm::integer_operation(KernelIntegerOperator::Add, vec![root.clone(), root])
                    .unwrap();
        }
        for source in [from, Variable(991951)] {
            let replacement = IntegerTerm::Variable(Variable(991952));
            let renamings = BTreeMap::new();
            let mut rewrite =
                TermRewrite::for_integer_variables(source, &replacement, false, &renamings);
            let exports = KernelTermExport::machine_export_count();
            let (actual, work) = crate::instrumentation::measure_deterministic_work(|| {
                rewrite.shared_integer_operand(&root).unwrap()
            });
            assert!(work <= 8 * (size + 1) + 64, "size={size}, work={work}");
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(!root.has_cached_native_argument());
            assert!(!actual.has_cached_native_argument());
            if source != from {
                assert_eq!(actual.id(), root.id());
            }
        }
    }
}

#[test]
fn retained_machine_observation_rewrites_keep_growing_numeric_dags_shared() {
    let _session = VerificationSession::enter();
    for size in [16, 64, 256] {
        let from = Variable(991980);
        let format = MachineIntegerType::UInt64;
        let mut operand = KernelTerm::variable(KernelType::Program(format.program_type()), from);
        for _ in 0..size {
            operand = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [operand.clone(), operand],
            );
        }
        let input = IntegerTerm::Machine(
            SharedMachineIntegerTerm::from_shared(format, operand.clone()).unwrap(),
        );
        let root = KernelTermImport::default().integer(&input.into());
        for variable in [from, Variable(991981)] {
            let source = MachineTerm::Variable(variable);
            let replacement = MachineTerm::Variable(Variable(991982));
            let mut rewrite = TermRewrite::for_bits_checked(&source, &replacement);
            let exports = KernelTermExport::machine_export_count();
            let was_cached = root.has_cached_native_argument();
            let (actual, work) = crate::instrumentation::measure_deterministic_work(|| {
                rewrite.shared_integer_operand(&root).unwrap()
            });
            assert!(work <= 30 * (size + 1) + 128, "size={size}, work={work}");
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert_eq!(root.has_cached_native_argument(), was_cached);
            assert!(!operand.has_cached_native_argument());
            if variable != from {
                assert_eq!(actual.id(), root.id());
            }
        }
    }
}

#[test]
fn retained_integer_conditionals_share_different_guards_with_common_prefixes() {
    let _session = VerificationSession::enter();
    for size in [16_usize, 64, 256] {
        let from = Variable(995200);
        let mut guard = KernelTerm::variable(KernelType::Bool, Variable(995201));
        let mut root = KernelTerm::variable(KernelType::Integer, from);
        for index in 0..size {
            guard = KernelTerm::boolean_equal_raw([
                guard,
                KernelTerm::variable(KernelType::Bool, Variable(996000 + index as u64)),
            ]);
            let no = KernelTerm::integer_operation(
                KernelIntegerOperator::Add,
                vec![root.clone(), KernelTerm::integer_literal(1.into())],
            )
            .unwrap();
            root = KernelTerm::integer_if_raw([guard.clone(), root, no]);
        }
        for source in [from, Variable(997000)] {
            let replacement = IntegerTerm::Variable(Variable(997001));
            let renamings = BTreeMap::new();
            let mut rewrite =
                TermRewrite::for_integer_variables(source, &replacement, false, &renamings);
            let exports = KernelTermExport::machine_export_count();
            let (actual, work) = crate::instrumentation::measure_deterministic_work(|| {
                rewrite.shared_integer_operand(&root).unwrap()
            });
            assert!(work <= 48 * (size + 1) + 128, "size={size}, work={work}");
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(!root.has_cached_native_argument());
            assert!(!guard.has_cached_native_argument());
            assert!(!actual.has_cached_native_argument());
            assert!(rewrite.refusal().is_none());
            if source != from {
                assert_eq!(actual.id(), root.id());
            }
        }
    }
}

#[test]
fn exact_observation_rewrite_uses_retained_integer_dags() {
    let _session = VerificationSession::enter();
    let signed = MachineIntegerType::Int32;
    let unsigned = MachineIntegerType::UInt32;
    let wide = MachineIntegerType::Int64;
    let variable = Variable(992840);
    let word = KernelTerm::variable(KernelType::Program(signed.program_type()), variable);
    let widened =
        KernelTerm::machine_cast_shared(MachineCastSpelling::Generic, signed, wide, word.clone());
    let observe = |format, root| {
        let value: SharedIntegerTerm =
            IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(format, root).unwrap())
                .into();
        let common = KernelTermImport::default().integer(&value);
        (value, common)
    };
    let (source, _) = observe(signed, word.clone());
    let (_, widened) = observe(wide, widened);
    let (_, other) = observe(unsigned, word.with_machine_observation_type(unsigned));
    let replacement: SharedIntegerTerm = IntegerTerm::var(Variable(992841)).into();
    let equality = Proposition::condition_is(
        ConditionTerm::IntegerEqual(source, replacement.clone()),
        true,
    );
    let add = |left, right| {
        KernelTerm::integer_operation(KernelIntegerOperator::Add, vec![left, right]).unwrap()
    };
    let compare = |left, right| {
        KernelTerm::integer_comparison(IntegerComparisonOperator::LessEqual, [left, right]).unwrap()
    };
    for size in [16, 64, 256] {
        let mut left = widened.clone();
        let mut expected = replacement.mathematical_root().unwrap().clone();
        for _ in 0..size {
            left = add(left.clone(), left);
            expected = add(expected.clone(), expected);
        }
        let comparison = compare(left.clone(), other.clone());
        let goal = Proposition::condition_is(
            StoredConditionTerm::from_root(comparison.clone()).unwrap(),
            false,
        );
        let mut previous_work = None;
        for unrelated in [0, 128, 512] {
            let mut facts = crate::kernel::proof::PureFactStore::default();
            for i in 0..unrelated {
                facts = facts.with_fact(Proposition::condition_is(
                    ConditionTerm::IntegerEqual(
                        IntegerTerm::var(Variable(994000 + i)).into(),
                        IntegerTerm::constant_i64(1).into(),
                    ),
                    true,
                ));
            }
            let facts = facts.with_fact(equality.clone());
            let exports = KernelTermExport::integer_export_count();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.check_equality_rewrite(&goal, &equality).unwrap()
            });
            assert!(work <= 8 * (size + 1) + 64, "size={size}, work={work}");
            let Proposition::ConditionIs(result, false) = result.proposition() else {
                panic!("comparison with original truth marker");
            };
            assert_eq!(
                result.root(),
                Some(&compare(expected.clone(), other.clone()))
            );
            assert_eq!(KernelTermExport::integer_export_count(), exports);
            assert!(!comparison.has_cached_native_argument());
            assert!(!left.has_cached_native_argument());
            if let Some(previous) = previous_work {
                assert_eq!(work, previous, "size={size}, unrelated={unrelated}");
            }
            previous_work = Some(work);
        }
    }
}
