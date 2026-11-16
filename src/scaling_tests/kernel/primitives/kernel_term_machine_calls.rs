use super::*;
#[test]
fn machine_call_roots_retain_growing_shared_arguments_without_exports() {
    let mut work = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut operand =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(995803));
        let exports = KernelTermExport::machine_export_count();
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                operand = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [operand.clone(), operand],
                );
                let application = SharedPureApplication::intern(
                    "f".into(),
                    vec![PureFunctionArgument::SharedMachine(
                        SharedMachineIntegerTerm::from_shared(format, operand.clone()).unwrap(),
                    )],
                );
                let root = KernelTermImport::default().machine_call(format, &application);
                assert_eq!(root.children()[0], operand, "prefix {index}");
                assert!(
                    std::ptr::eq(
                        root.machine_conversion_leaf().unwrap(),
                        application.native_call(),
                    ),
                    "the already-produced payload is borrowed"
                );
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work.push(measured);
    }
    assert!(
        work[0] > 0 && work[1] <= 5 * work[0] && work[2] <= 5 * work[1],
        "{work:?}"
    );
}

#[test]
fn common_call_numeric_identity_is_linear_cold_and_constant_warm() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut root =
            KernelTerm::variable(KernelType::Program(format.program_type()), Variable(995830));
        for _ in 0..size {
            root = KernelTerm::intern(
                KernelType::Program(format.program_type()),
                KernelTermNode::Call {
                    name: "identity_chain".into(),
                    arguments: vec![root.clone(), root],
                },
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (identity, cold) = crate::instrumentation::measure_deterministic_work(|| {
            SharedMachineIntegerTerm::observe_shared(format, root.clone()).unwrap()
        });
        let (_, warm) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                SharedMachineIntegerTerm::observe_shared(format, root.clone()).unwrap(),
                identity
            );
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(matches!(root.node(), KernelTermNode::Call { .. }));
        samples.push((cold, warm));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].0 <= 5 * pair[0].0, "{samples:?}");
        assert_eq!(pair[1].1, pair[0].1, "{samples:?}");
    }
}

#[test]
fn common_call_import_keeps_growing_shared_arguments_without_exporting() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut root =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(995910));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                let argument = SharedMachineIntegerTerm::from_shared(format, root).unwrap();
                let native = MachineTerm::ClickFunctionApplication {
                    name: "imported_call".into(),
                    arguments: vec![PureFunctionArgument::SharedMachine(argument)],
                };
                root = KernelTermImport::default().machine(format, &native);
                assert!(matches!(root.node(), KernelTermNode::Call { .. }));
                assert_eq!(KernelTermImport::default().machine(format, &native), root);
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples[1] <= 5 * samples[0] && samples[2] <= 5 * samples[1],
        "{samples:?}"
    );
}

#[test]
fn pthread_handle_leaf_lookup_is_independent_of_other_handles() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut import = KernelTermImport::default();
        let unrelated = (0..size)
            .map(|id| {
                import.machine(
                    MachineIntegerType::UInt64,
                    &MachineTerm::ThreadHandle(ThreadHandleId(id)),
                )
            })
            .collect::<Vec<_>>();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let native = MachineTerm::ThreadHandle(ThreadHandleId(999001));
            let root = import.machine(MachineIntegerType::UInt64, &native);
            assert!(root.children().is_empty());
            assert_eq!(KernelTermExport::machine(&root).unwrap(), native);
            assert_eq!(import.machine(MachineIntegerType::UInt64, &native), root);
        });
        assert_eq!(unrelated.len(), size as usize);
        samples.push(work);
    }
    assert!(samples[0] > 0);
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn forwarded_handle_lookup_ignores_equality_class_and_context_population() {
    use crate::kernel::{ConditionTerm, Proposition, PureFactContext};
    let mut samples = Vec::new();
    for chain in [false, true] {
        for size in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let handle = ThreadHandleId(998001);
            let word = MachineTerm::ThreadHandle(handle);
            let variable = |index| MachineTerm::Variable(Variable(1009000 + index));
            let equality = |left, right| {
                Proposition::ConditionIs(ConditionTerm::uint64_equal(left, right), true)
            };
            let mut facts =
                PureFactContext::new().assume_proposition(equality(variable(0), word.clone()));
            for index in 1..size {
                let source = if chain {
                    variable(index - 1)
                } else {
                    word.clone()
                };
                facts = facts.assume_proposition(equality(variable(index), source));
                facts = facts.assume_proposition(equality(
                    variable(size + index),
                    MachineTerm::ThreadHandle(ThreadHandleId(index)),
                ));
            }
            let value = ProgramValue::UInt64(variable(size - 1));
            let missing = ProgramValue::UInt64(variable(4 * size));
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                assert_eq!(
                    ThreadHandleId::resolve_program_value(&value, &facts),
                    Some(handle)
                );
                assert_eq!(
                    ThreadHandleId::resolve_program_value(&missing, &facts),
                    None
                );
            });
            samples.push(work);
        }
    }
    assert!(samples[0] > 0);
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "{samples:?}"
    );
}
