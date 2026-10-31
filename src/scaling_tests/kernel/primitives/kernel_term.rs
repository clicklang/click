use super::*;

#[test]
fn shared_term_bridges_visit_nodes_once_beside_unrelated_terms() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(900_000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 32, 64, 128] {
            let mut source: SharedIntegerTerm = IntegerTerm::Variable(Variable(901_000)).into();
            for _ in 0..size {
                source = IntegerTerm::Add(source.clone(), source).into();
            }
            let ((imported, restored), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    let imported = KernelTermImport::default().integer(&source);
                    let restored = KernelTermExport::default().integer(&imported).unwrap();
                    (imported, restored)
                });
            assert_eq!(restored, source);
            assert_eq!(imported.ty(), &KernelType::Integer);
            assert!(
                work <= 12 * (size + 1),
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}
