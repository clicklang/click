use super::*;
use crate::kernel::{KernelTerm, KernelTermExport, KernelType, MachineBinaryOp, Variable};

#[test]
fn sign_bit_readings_retain_growing_shared_prefixes() {
    let samples = [16usize, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let mut term = KernelTerm::variable(
            KernelType::Program(Ty::UInt32.program_type()),
            Variable(189221),
        );
        let zero = MachineTerm::constant(0);
        let context = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                term = KernelTerm::machine_binary_shared(
                    Ty::UInt32,
                    MachineBinaryOp::Add,
                    [term.clone(), term.clone()],
                );
                let cast = KernelTerm::machine_cast_shared(
                    Encoding::Generic,
                    Ty::UInt32,
                    Ty::Int32,
                    term.clone(),
                );
                let query = condition_for_operand_views(
                    Ty::Int32,
                    R::LessThan,
                    [View::Shared(&cast), View::Legacy(&zero)],
                );
                assert!(query.names_sign_cast32());
                let equivalents = context.sign_bit_equivalents(&query).unwrap();
                assert_eq!(equivalents.len(), 1);
                let view = comparison(&equivalents[0]).unwrap();
                assert_eq!(view.format, Ty::UInt32);
                assert_eq!(view.relation, Relation::Less);
                assert_eq!(
                    view.operands[1]
                        .operand_view()
                        .retain(Ty::UInt32)
                        .shared_operand(),
                    Some(&term)
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
