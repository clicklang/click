use super::*;

#[test]
fn shared_wide_constant_capture_scales_with_dag_and_selected_sources() {
    let mut samples = Vec::new();
    for size in [8u32, 32, 96] {
        for unrelated in [0, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let ty = MachineIntegerType::UInt64;
            let variable = |id| KernelTerm::variable(KernelType::C(ty.c_type()), Variable(id));
            let mut root = variable(998771);
            let source = Proposition::ConditionIs(
                ConditionTerm::integer_equal(
                    IntegerTerm::Machine(
                        SharedMachineIntegerTerm::from_shared(ty, root.clone()).unwrap(),
                    ),
                    IntegerTerm::constant(1.into()),
                ),
                true,
            );
            let mut parent = PureFactContext::new();
            for i in 0..unrelated {
                parent = parent.assume_condition(
                    ConditionTerm::int64_equal(
                        Bitvector32Term::Variable(Variable(998800 + i)),
                        Bitvector32Term::Int64Constant(3),
                    ),
                    true,
                );
            }
            let child = parent.clone().assume_proposition(source.clone());
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [root.clone(), root],
                );
            }
            let operand = SharedMachineIntegerTerm::from_shared(ty, root).unwrap();
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                let read = |context: &PureFactContext| {
                    capture_implicit_reasoning_provenance(|| {
                        context.wide_constant_from_equalities_view(operand.operand_view())
                    })
                };
                assert_eq!(read(&parent), None);
                let (value, sources) = collect_reasoning_provenance(|| read(&child));
                assert_eq!(value, Some(2u64.wrapping_pow(size)));
                assert!(sources.contains(&source));
                assert_eq!(read(&parent), None);
            });
            assert!(!operand.has_boxed_operand());
            samples.push((size as usize, unrelated, work));
        }
    }
    for pair in samples.chunks_exact(2) {
        assert!(pair[1].2 <= pair[0].2 + 32, "{samples:?}");
    }
    for pair in samples.chunks_exact(2).collect::<Vec<_>>().windows(2) {
        let (small, _, sw) = pair[0][0];
        let (large, _, lw) = pair[1][0];
        assert!(lw * small <= sw * large * 2, "{samples:?}");
    }
}
