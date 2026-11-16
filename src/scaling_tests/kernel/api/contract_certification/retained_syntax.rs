use super::*;
#[test]
fn retained_syntax_comparison_visits_each_shared_pair_once() {
    let mut work = Vec::new();
    for depth in [8, 32, 96] {
        let _session = VerificationSession::enter();
        let prefix = || {
            let mut root = retained_leaf(7);
            for _ in 0..depth {
                root = KernelTerm::machine_binary_shared(
                    MachineIntegerType::UInt64,
                    MachineBinaryOp::Add,
                    [root.clone(), root],
                );
            }
            condition(root)
        };
        let (left, right) = (prefix(), prefix());
        let exports = KernelTermExport::machine_export_count();
        let (equal, cost) =
            crate::instrumentation::measure_deterministic_work(|| conditions_equal(&left, &right));
        assert!(equal);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work.push(cost);
    }
    for pair in work.windows(2) {
        assert!(pair[1] <= 4 * pair[0] + 32, "{work:?}");
    }
}

#[test]
fn algebraic_call_certification_visits_retained_numeric_pairs_once() {
    use crate::kernel::{AlgebraicTermNode, AlgebraicType, SharedPureApplication, Variable};
    let mut samples = Vec::new();
    for depth in [8, 32, 96] {
        let _session = VerificationSession::enter();
        let variable = AlgebraicTerm {
            algebraic_type: AlgebraicType::parameter("T".into()),
            node: AlgebraicTermNode::Variable(Variable(995952)),
        };
        let build = || {
            let application = SharedPureApplication::intern(
                "length".into(),
                vec![A::Algebraic(variable.clone())],
            );
            let mut root = crate::kernel::KernelTermImport::default()
                .machine_call(MachineIntegerType::UInt64, &application);
            for _ in 0..depth {
                root = KernelTerm::machine_binary_shared(
                    MachineIntegerType::UInt64,
                    MachineBinaryOp::Add,
                    [root.clone(), root],
                );
            }
            AlgebraicTerm {
                algebraic_type: variable.algebraic_type.clone(),
                node: AlgebraicTermNode::PureFunctionApplication {
                    name: "wrap".into(),
                    arguments: vec![A::SharedMachine(
                        SharedMachineIntegerTerm::from_shared(MachineIntegerType::UInt64, root)
                            .unwrap(),
                    )],
                },
            }
        };
        let (left, right) = (build(), build());
        let exports = KernelTermExport::machine_export_count();
        let (equal, work) =
            crate::instrumentation::measure_deterministic_work(|| algebraic_equal(&left, &right));
        assert!(equal);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= 4 * pair[0] + 32, "{samples:?}");
    }
}

#[test]
fn numeric_call_certification_refuses_unsupported_float_syntax_without_exporting_it() {
    let mut previous = None;
    for depth in [8, 32, 128] {
        let _session = VerificationSession::enter();
        let mut source = MachineTerm::Variable(Variable(995953));
        for _ in 0..depth {
            source = MachineTerm::Float32Negate(Box::new(source));
        }
        let native = MachineTerm::ClickFunctionApplication {
            name: "numeric_boundary".into(),
            arguments: vec![A::Value(ProgramValue::Float32(source))],
        };
        let root =
            crate::kernel::KernelTermImport::default().machine(MachineIntegerType::Int32, &native);
        assert!(!Comparison::default().machine(Operand::Legacy(&native), Operand::Legacy(&native)));
        let exports = KernelTermExport::float_export_count();
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            Comparison::default().machine(Operand::Shared(&root), Operand::Legacy(&native))
        });
        assert!(!equal);
        assert_eq!(KernelTermExport::float_export_count(), exports);
        if let Some(previous) = previous {
            assert_eq!(work, previous, "refusal must not walk the float argument");
        }
        previous = Some(work);
    }
}

#[test]
fn integer_conversion_certification_keeps_native_refusal_without_exporting_the_operand() {
    use crate::kernel::IntegerTerm;
    let mut previous = None;
    for depth in [8, 32, 128] {
        let _session = VerificationSession::enter();
        let mut source = IntegerTerm::Variable(Variable(995954));
        for _ in 0..depth {
            source = IntegerTerm::Add(source.into(), IntegerTerm::constant_i64(1).into());
        }
        let native = MachineTerm::IntegerToMachine {
            destination: MachineIntegerType::Int32,
            value: source.into(),
        };
        let root =
            crate::kernel::KernelTermImport::default().machine(MachineIntegerType::Int32, &native);
        assert!(!Comparison::default().machine(Operand::Legacy(&native), Operand::Legacy(&native)));
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            Comparison::default().machine(Operand::Shared(&root), Operand::Legacy(&native))
        });
        assert!(!equal);
        if let Some(previous) = previous {
            assert_eq!(work, previous, "refusal must not walk the Integer operand");
        }
        previous = Some(work);
        assert!(Comparison::default().machine(Operand::Shared(&root), Operand::Shared(&root)));
    }
}

#[test]
fn logical_argument_refusals_do_not_convert_growing_boolean_or_algebraic_trees() {
    use crate::kernel::{AlgebraicTermNode, AlgebraicType};
    let mut previous = None;
    for depth in [8, 32, 128] {
        let _session = VerificationSession::enter();
        let atom = ConditionTerm::Variable(Variable(995955));
        let mut condition = atom.clone();
        let variable = AlgebraicTerm {
            algebraic_type: AlgebraicType::parameter("T".into()),
            node: AlgebraicTermNode::Variable(Variable(995956)),
        };
        let mut algebraic = variable.clone();
        for _ in 0..depth {
            condition = ConditionTerm::BoolIf {
                condition: Box::new(atom.clone()),
                then_condition: Box::new(condition),
                else_condition: Box::new(ConditionTerm::Constant(false)),
            };
            algebraic = AlgebraicTerm {
                algebraic_type: variable.algebraic_type.clone(),
                node: AlgebraicTermNode::If {
                    condition: Box::new(atom.clone()),
                    then_term: Box::new(algebraic),
                    else_term: Box::new(variable.clone()),
                },
            };
        }
        let boolean = crate::kernel::KernelTermImport::default().condition(&condition);
        let root = crate::kernel::KernelTermImport::default().algebraic(&algebraic);
        let native = A::Value(ProgramValue::Bool(MachineTerm::bool_cast(
            MachineIntegerType::UInt8,
            condition,
        )));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(!Comparison::default().call_argument(
                CallArgument::Shared(&boolean),
                CallArgument::Native(&native),
            ));
            assert!(!Comparison::default().mixed_algebraic(&root, &algebraic));
        });
        if let Some(previous) = previous {
            assert_eq!(work, previous, "refusal must not walk the logical payload");
        }
        previous = Some(work);
    }
}
