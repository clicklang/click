use super::*;

fn growing_prefixes(unresolved: bool, cancel: bool) {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let base = KernelTerm::variable(KernelType::C(ty.c_type()), Variable(982001));
        let other = if unresolved {
            KernelTerm::variable(KernelType::C(ty.c_type()), Variable(982002))
        } else {
            base.clone()
        };
        let zero =
            crate::kernel::KernelTermImport::default().machine(ty, &Bitvector32Term::constant(0));
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
                        Bitvector32Term::Variable(Variable(982010 + n as u64)),
                        Bitvector32Term::constant(n as u32),
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
