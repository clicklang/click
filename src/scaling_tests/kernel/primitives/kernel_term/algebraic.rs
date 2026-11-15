use super::*;

#[test]
fn algebraic_constructor_prefixes_import_and_export_linearly() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let leaf = KernelMatch::test_scrutinee(vec![AlgebraicValueType::Algebraic {
            name: "MatchScope".into(),
            arguments: vec![],
        }]);
        let ty = leaf.algebraic_type.clone();
        let mut source = leaf;
        for _ in 0..size {
            source = AlgebraicTerm {
                algebraic_type: ty.clone(),
                node: AlgebraicTermNode::Constructor {
                    variant: "Arm".into(),
                    fields: vec![AlgebraicValue::Algebraic(source)],
                },
            };
        }
        let exports = KernelTermExport::algebraic_export_count();
        let (root, work) = crate::instrumentation::measure_deterministic_work(|| {
            KernelTermImport::default().algebraic(&source)
        });
        assert!(work <= 20 * size + 100, "size={size} work={work}");
        assert_eq!(KernelTermExport::algebraic_export_count(), exports);
        let (native, work) = crate::instrumentation::measure_deterministic_work(|| {
            KernelTermExport::default().algebraic(&root).unwrap()
        });
        assert_eq!(native, source);
        assert!(work <= 20 * size + 100, "size={size} work={work}");
    }
}
