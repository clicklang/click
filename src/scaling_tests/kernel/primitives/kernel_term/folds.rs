use super::*;

#[test]
fn fold_payload_construction_retains_growing_shared_bodies_with_constant_work() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|n| KernelTerm::variable(KernelType::Integer, Variable(950_000 + n)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut body = KernelTerm::variable(KernelType::Integer, Variable(960_000));
            for _ in 0..size {
                body = KernelTerm::integer_operation(
                    KernelIntegerOperator::Add,
                    vec![body.clone(), body],
                )
                .unwrap();
            }
            let zero = KernelTerm::integer_literal(0.into());
            let before = KernelTermExport::machine_export_count();
            let ((fold, copy), work) = crate::instrumentation::measure_deterministic_work(|| {
                let fold = KernelFold::new(
                    KernelFoldIndex::Integer,
                    Variable(960_000),
                    Variable(960_001),
                    [zero.clone(), zero.clone(), zero.clone(), body.clone()],
                )
                .unwrap();
                let copy = fold.clone();
                assert_eq!(fold, copy);
                (fold, copy)
            });
            assert_eq!(fold.arguments[3], body);
            assert_eq!(copy.arguments[3], body);
            assert_eq!(work, 1, "size={size}, unrelated={unrelated}");
            assert_eq!(KernelTermExport::machine_export_count(), before);
        }
    }
}
