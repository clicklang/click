use super::*;
use crate::kernel::{KernelTerm, KernelTermExport, KernelType, SharedMachineIntegerTerm};

#[test]
fn shared_order_reflexivity_keeps_zero_addend_prefixes_shared() {
    check_zero_prefixes(false, false);
}

#[test]
fn unresolved_shared_order_keeps_zero_addend_prefixes_shared() {
    check_zero_prefixes(true, false);
}

#[test]
fn shared_order_reuses_cancelled_prefixes() {
    check_zero_prefixes(false, true);
}

#[test]
fn unresolved_shared_order_reuses_cancelled_prefixes() {
    check_zero_prefixes(true, true);
}

fn check_zero_prefixes(unresolved: bool, cancellation: bool) {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let base =
            KernelTerm::variable(KernelType::Program(format.program_type()), Variable(997631));
        let zero = KernelTermImport::default()
            .machine_arithmetic(format, &0u32.into())
            .unwrap();
        let right = if unresolved {
            KernelTerm::variable(KernelType::Program(format.program_type()), Variable(997632))
        } else {
            base.clone()
        };
        let mut root = base.clone();
        let observed = |root| {
            IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(format, root).unwrap())
        };
        let mut context = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for n in 0..size {
                root = if cancellation {
                    let added = KernelTerm::machine_binary_shared(
                        format,
                        Op::Add,
                        [root.clone(), right.clone()],
                    );
                    KernelTerm::machine_binary_shared(format, Op::Subtract, [added, right.clone()])
                } else {
                    KernelTerm::machine_binary_shared(format, Op::Add, [root.clone(), zero.clone()])
                };
                context = context.assume_condition(
                    ConditionTerm::equal(
                        MachineTerm::Variable(Variable(997640 + n as u64)),
                        (n as u32).into(),
                    ),
                    true,
                );
                let query = ConditionTerm::integer_less_than(
                    observed(root.clone()),
                    observed(right.clone()),
                );
                assert_eq!(
                    context.decide(&query),
                    if unresolved { None } else { Some(false) }
                );
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 5 + 100, "{samples:?}");
    }
}
