use super::*;

#[test]
fn growing_wide_order_paths_reuse_shared_prefixes() {
    use crate::kernel::MachineOperandView as V;
    let mut samples = Vec::new();
    for count in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::UInt64;
        let variable = |id| KernelTerm::variable(KernelType::C(ty.c_type()), Variable(id));
        let mut root = variable(988001);
        let zero = crate::kernel::KernelTermImport::default()
            .machine(ty, &Bitvector32Term::uint64_constant(0));
        let observe =
            |term| IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(ty, term).unwrap());
        let mut context = PureFactContext::new().defer_non_exact_condition_reasoning();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for n in 0..count {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [root, zero.clone()],
                );
                let middle = variable(988010 + 2 * n);
                let upper = variable(988011 + 2 * n);
                context = context.assume_condition(
                    ConditionTerm::integer_less_equal(
                        observe(root.clone()),
                        observe(middle.clone()),
                    ),
                    true,
                );
                context = context.assume_condition(
                    ConditionTerm::integer_less_than(observe(middle), observe(upper.clone())),
                    true,
                );
                let path = context
                    .exact_wide_order_path_evidence(V::Shared(&root), V::Shared(&upper), true, ty)
                    .expect("two selected edges");
                assert_eq!(path.len(), 2);
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
