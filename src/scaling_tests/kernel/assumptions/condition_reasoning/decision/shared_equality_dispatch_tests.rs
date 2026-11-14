use super::*;

fn growing_prefixes(unresolved: bool, cancel: bool) {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let base = KernelTerm::variable(KernelType::Program(ty.c_type()), Variable(982001));
        let other = if unresolved {
            KernelTerm::variable(KernelType::Program(ty.c_type()), Variable(982002))
        } else {
            base.clone()
        };
        let zero =
            crate::kernel::KernelTermImport::default().machine(ty, &MachineTerm::constant(0));
        let observe =
            |root| IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(ty, root).unwrap());
        let mut root = base.clone();
        let mut context = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for n in 0..size {
                root = if cancel {
                    let sum = KernelTerm::machine_binary_shared(ty, Op::Add, [root, other.clone()]);
                    KernelTerm::machine_binary_shared(ty, Op::Subtract, [sum, other.clone()])
                } else {
                    KernelTerm::machine_binary_shared(ty, Op::Add, [root, zero.clone()])
                };
                context = context.assume_condition(
                    ConditionTerm::equal(
                        MachineTerm::Variable(Variable(982010 + n as u64)),
                        MachineTerm::constant(n as u32),
                    ),
                    true,
                );
                let goal =
                    ConditionTerm::integer_equal(observe(root.clone()), observe(other.clone()));
                assert_eq!(
                    context.decide(&goal),
                    if unresolved { None } else { Some(true) }
                );
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|p| p[1] <= p[0] * 5 + 100),
        "unresolved={unresolved}, cancel={cancel}: {samples:?}"
    );
}

#[test]
fn successful_zero_prefixes_reuse_word_classes() {
    growing_prefixes(false, false);
}
#[test]
fn unresolved_zero_prefixes_reuse_word_classes() {
    growing_prefixes(true, false);
}
#[test]
fn successful_cancellation_prefixes_reuse_word_classes() {
    growing_prefixes(false, true);
}
#[test]
fn unresolved_cancellation_prefixes_reuse_word_classes() {
    growing_prefixes(true, true);
}

#[test]
fn wide_mask_queries_retain_growing_shared_operands() {
    use crate::kernel::MachineOperandView as V;
    use crate::kernel::machine_integer::comparison::condition_for_operand_views;
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::UInt64;
        let literal = |n| {
            crate::kernel::KernelTermImport::default()
                .machine_arithmetic(ty, &MachineTerm::uint64_constant(n))
                .unwrap()
        };
        let mut root = KernelTerm::variable(KernelType::Program(ty.c_type()), Variable(983101));
        let one = literal(1);
        let mask = literal(8);
        let zero = literal(0);
        let bound = MachineTerm::uint64_constant(8);
        let mut context = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(ty, Op::Multiply, [root, one.clone()]);
                let guard = condition_for_operand_views(
                    ty,
                    CompareRelation::LessThan,
                    [V::Shared(&root), V::Legacy(&bound)],
                );
                context = context.assume_condition(guard, true);
                let masked = KernelTerm::machine_binary_shared(
                    ty,
                    Op::BitwiseAnd,
                    [root.clone(), mask.clone()],
                );
                let goal = condition_for_operand_views(
                    ty,
                    CompareRelation::Equal,
                    [V::Shared(&masked), V::Shared(&zero)],
                );
                assert_eq!(context.decide(&goal), Some(true));
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|p| p[1] <= p[0] * 5 + 100),
        "{samples:?}"
    );
}
