use super::*;
use crate::kernel::{KernelTerm, KernelType, MachineBinaryOp};

#[test]
fn adjacent_bound_queries_retain_shared_prefixes_in_changing_contexts() {
    let samples = [16usize, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut root = KernelTerm::variable(KernelType::Program(format.c_type()), Variable(189321));
        let mut context = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for n in 0..size {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [root.clone(), root.clone()],
                );
                context = context.assume_condition(
                    ConditionTerm::equal(
                        MachineTerm::Variable(Variable(189330 + n as u64)),
                        MachineTerm::constant(n as u32),
                    ),
                    true,
                );
                assert_eq!(
                    context.decide_exact_word_constant_order(
                        &query(format, CompareRelation::LessThan, V::Shared(&root), 10),
                        format
                    ),
                    None
                );
                assert_eq!(
                    context.decide_exact_word_constant_order(
                        &query(
                            format,
                            CompareRelation::LessEqual,
                            V::Shared(&root),
                            i32::MAX as u32
                        ),
                        format
                    ),
                    Some(true)
                );
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        (size, work)
    });
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small <= sw * large * 2, "{samples:?}");
    }
}
