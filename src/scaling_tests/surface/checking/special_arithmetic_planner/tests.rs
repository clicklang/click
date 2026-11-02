use super::*;

#[test]
fn shared_interval_planning_keeps_operands_and_checks_selected_bounds() {
    use crate::kernel::{IntegerTerm, KernelTerm, KernelType, SharedMachineIntegerTerm, Variable};
    let mut samples = Vec::new();
    for size in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let mut root = KernelTerm::variable(KernelType::C(ty.c_type()), Variable(986301));
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                ty,
                MachineBinaryOp::Add,
                [root.clone(), root.clone()],
            );
        }
        let machine = SharedMachineIntegerTerm::from_shared(ty, root).unwrap();
        let observed = IntegerTerm::Machine(machine.clone());
        let exact = IntegerTerm::Add(
            observed.clone().into(),
            IntegerTerm::constant(1.into()).into(),
        );
        let domain = Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::IntegerLessEqual(
                    exact.clone().into(),
                    IntegerTerm::constant(i32::MAX.into()).into(),
                ),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::IntegerGreaterEqual(
                    exact.into(),
                    IntegerTerm::constant(i32::MIN.into()).into(),
                ),
                true,
            )),
        );
        let bounds = |lower: i32, upper: i32| {
            vec![
                Proposition::ConditionIs(
                    ConditionTerm::IntegerGreaterEqual(
                        observed.clone().into(),
                        IntegerTerm::constant(lower.into()).into(),
                    ),
                    true,
                ),
                Proposition::ConditionIs(
                    ConditionTerm::IntegerLessEqual(
                        observed.clone().into(),
                        IntegerTerm::constant(upper.into()).into(),
                    ),
                    true,
                ),
            ]
        };
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let premises = bounds(0, 100);
            let plan = plan_special_arithmetic_certificate(&domain, &premises).unwrap();
            assert_eq!(plan.check(&domain, &premises), Ok(()));
            let insufficient = bounds(i32::MAX, i32::MAX);
            let plan = plan_special_arithmetic_certificate(&domain, &insufficient).unwrap();
            assert!(plan.check(&domain, &insufficient).is_err());
            assert!(!machine.has_boxed_operand());
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
