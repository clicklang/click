#[test]
fn retained_fold_affine_matching_counts_shared_dag_occurrences() {
    let mut samples = Vec::new();
    for depth in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let x = KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(999201));
        let y = KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(999202));
        let mut left = KernelTerm::machine_binary_shared(format, Op::Add, [x.clone(), y.clone()]);
        let mut right = KernelTerm::machine_binary_shared(format, Op::Add, [y, x]);
        for _ in 0..depth {
            left = KernelTerm::machine_binary_shared(format, Op::Add, [left.clone(), left]);
            right = KernelTerm::machine_binary_shared(format, Op::Add, [right.clone(), right]);
        }
        let left = SharedMachineIntegerTerm::from_shared(format, left).unwrap();
        let right = SharedMachineIntegerTerm::from_shared(format, right).unwrap();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                retained_fold_affine_form(left.operand_view()),
                retained_fold_affine_form(right.operand_view())
            );
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{samples:?}");
    }
}

#[test]
fn affine_occurrence_counts_wrap_only_at_the_word_width() {
    let _session = VerificationSession::enter();
    let format = MachineIntegerType::Int32;
    let mut root = KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(999250));
    for _ in 0..31 {
        root = KernelTerm::machine_binary_shared(format, Op::Add, [root.clone(), root]);
    }
    let exports = KernelTermExport::machine_export_count();
    let (atoms, constant) =
        retained_fold_affine_form(crate::kernel::MachineOperandView::Shared(&root));
    assert_eq!(constant, 0);
    assert_eq!(atoms.len(), 1);
    assert_eq!(atoms.values().next(), Some(&(1u32 << 31)));
    root = KernelTerm::machine_binary_shared(format, Op::Add, [root.clone(), root]);
    let (atoms, constant) =
        retained_fold_affine_form(crate::kernel::MachineOperandView::Shared(&root));
    assert!(atoms.is_empty());
    assert_eq!(constant, 0);
    assert_eq!(KernelTermExport::machine_export_count(), exports);
}

#[test]
fn fold_endpoint_constant_spines_do_not_rewalk_growing_prefixes() {
    let mut samples = Vec::new();
    for count in [16u64, 64, 256] {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let one = KernelTermImport::default().machine(format, &MachineTerm::constant(1));
        let mut root =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(999301));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..count {
                root = KernelTerm::machine_binary_shared(
                    format,
                    Op::Add,
                    [
                        root.clone(),
                        KernelTerm::variable(
                            KernelType::Program(ProgramType::Int32),
                            Variable(999302 + index),
                        ),
                    ],
                );
                let predecessor = KernelTerm::machine_binary_shared(
                    format,
                    Op::Subtract,
                    [root.clone(), one.clone()],
                );
                let wrapped =
                    KernelTerm::machine_binary_shared(format, Op::Add, [predecessor, one.clone()]);
                let left = SharedMachineIntegerTerm::from_shared(format, wrapped).unwrap();
                let right = SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap();
                let context = PureFactContext::new()
                    .assume_condition(ConditionTerm::Variable(Variable(999600 + index)), true);
                assert!(fold_endpoint_terms_proven_equal(&left, &right, &context));
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{samples:?}");
    }
}

#[test]
fn repeated_affine_equalities_reuse_the_previous_shared_roots() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256] {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let x = KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(999801));
        let y = KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(999802));
        let mut left = KernelTerm::machine_binary_shared(format, Op::Add, [x.clone(), y.clone()]);
        let mut right = KernelTerm::machine_binary_shared(format, Op::Add, [y, x]);
        for index in 0..size {
            let leaf = KernelTerm::variable(
                KernelType::Program(ProgramType::Int32),
                Variable(1000000 + index),
            );
            left = KernelTerm::machine_binary_shared(format, Op::Add, [left, leaf.clone()]);
            right = KernelTerm::machine_binary_shared(format, Op::Add, [right, leaf]);
        }
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                assert!(retained_fold_affine_equal(
                    crate::kernel::MachineOperandView::Shared(&left),
                    crate::kernel::MachineOperandView::Shared(&right)
                ));
                left = KernelTerm::machine_binary_shared(format, Op::Add, [left.clone(), left]);
                right = KernelTerm::machine_binary_shared(format, Op::Add, [right.clone(), right]);
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 6, "{samples:?}");
    }
}

#[test]
fn selected_endpoint_equality_looks_up_one_pair_in_growing_source_stars() {
    for format in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
        let mut samples = Vec::new();
        for count in [16u64, 64, 256] {
            let _session = VerificationSession::enter();
            let anchor = Variable(1001000);
            let mut context = PureFactContext::new();
            for index in 0..count {
                context = context.assume_condition(
                    ConditionTerm::machine_compare(
                        format,
                        CompareRelation::Equal,
                        MachineTerm::Variable(anchor),
                        MachineTerm::Variable(Variable(1001100 + index)),
                    ),
                    true,
                );
            }
            let root = |v| KernelTerm::variable(KernelType::Program(format.c_type()), v);
            let left = root(anchor);
            let right = root(Variable(1001100));
            let missing = root(Variable(1001500));
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                use crate::kernel::MachineOperandView as V;
                assert!(exact_fold_endpoint_equality(
                    format,
                    V::Shared(&left),
                    V::Shared(&right),
                    &context
                ));
                assert!(!exact_fold_endpoint_equality(
                    format,
                    V::Shared(&left),
                    V::Shared(&missing),
                    &context
                ));
                if format == MachineIntegerType::UInt64 {
                    let low_word = PureFactContext::new().assume_condition(
                        ConditionTerm::equal(
                            MachineTerm::Variable(anchor),
                            MachineTerm::Variable(Variable(1001500)),
                        ),
                        true,
                    );
                    assert!(!exact_fold_endpoint_equality(
                        format,
                        V::Shared(&left),
                        V::Shared(&missing),
                        &low_word
                    ));
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work <= samples[0] * 3),
            "{format:?}: {samples:?}"
        );
    }
}
