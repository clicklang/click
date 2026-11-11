// Scaling tests of `src/kernel/assumptions.rs` (module `exact_materialization_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn exact_materialization_work_scales_near_linearly_with_chain_length() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|length| {
            let chain = load_chain(length, 23);
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                exact_materialized_load_fixed_point(&chain)
            });
            assert_eq!(result, MachineTerm::constant(23));
            assert!(work > 0);
            (length, work)
        })
        .collect::<Vec<_>>();
    assert!(
        samples
            .windows(2)
            .all(|pair| pair[1].1 <= pair[0].1.saturating_mul(3)),
        "exact materialization grew faster than near-linearly: {samples:?}"
    );
}

#[test]
fn retained_materialization_equality_keeps_growing_indices_shared() {
    use crate::kernel::{KernelTerm, KernelTermExport, MachineBinaryOp};
    let format = MachineIntegerType::Int32;
    let root = |v| {
        KernelTerm::retained_machine_operand(
            format,
            MachineOperandView::Legacy(&MachineTerm::Variable(Variable(v))),
        )
    };
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let (mut a, mut b) = (root(994552), root(994553));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                a = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [a.clone(), a.clone()],
                );
                b = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [b.clone(), b.clone()],
                );
                let offset = |root| PointerOffsetTerm::Int32Scaled {
                    value: SharedMachineIntegerTerm::from_shared(format, root).unwrap(),
                    byte_width: 4,
                };
                assert!(!pointer_offsets_equal_after_exact_materialization(
                    &offset(a.clone()),
                    &offset(b.clone())
                ));
                // Different observation types retain the same native syntax;
                // exact correspondence must not be just DAG identity.
                assert!(crate::kernel::shared_machine_syntax_equal(
                    &a,
                    &a.with_machine_observation_type(MachineIntegerType::UInt32),
                ));
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|w| w[1] <= 5 * w[0] + 100),
        "{samples:?}"
    );
}
