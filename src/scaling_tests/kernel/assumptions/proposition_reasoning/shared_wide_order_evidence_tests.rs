use super::*;

#[test]
fn growing_order_paths_reuse_shared_prefixes() {
    use crate::kernel::MachineOperandView as V;
    for ty in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
        let mut samples = Vec::new();
        for count in [8, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let variable =
                |id| KernelTerm::variable(KernelType::Program(ty.c_type()), Variable(id));
            let mut root = variable(988001);
            let zero = crate::kernel::KernelTermImport::default().machine(
                ty,
                &MachineTerm::machine_constant(
                    crate::kernel::MachineIntegerConstant::from_signed(ty.format(), 0).unwrap(),
                ),
            );
            let observe = |term| {
                IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(ty, term).unwrap())
            };
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
                    if ty == MachineIntegerType::Int32 {
                        assert!(context.canonical_bound_holds_views(
                            V::Shared(&root),
                            V::Shared(&middle),
                            false
                        ));
                    }
                    context = context.assume_condition(
                        ConditionTerm::integer_less_than(observe(middle), observe(upper.clone())),
                        true,
                    );
                    let path = if ty == MachineIntegerType::Int32 {
                        context.exact_signed_order_source_path(
                            V::Shared(&root),
                            V::Shared(&upper),
                            true,
                        )
                    } else {
                        context.exact_wide_order_path_evidence(
                            V::Shared(&root),
                            V::Shared(&upper),
                            true,
                            ty,
                        )
                    }
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
}
