use super::tests::complete_source;
use super::*;
use crate::kernel::effective_type::{CAccessClass, CScalarClass};

#[test]
fn complete_pointer_import_retains_persistent_evidence_without_traversal() {
    for size in [16, 64, 256] {
        let mut source = complete_source();
        let class = CAccessClass::Scalar(CScalarClass::Int);
        let mut evidence = ObjectTypeEvidence::parameter(class.clone(), 0, 1000010, true);
        for index in 1..size {
            evidence = evidence.merge(&ObjectTypeEvidence::parameter(
                class.clone(),
                index,
                1000010,
                true,
            ));
        }
        Arc::make_mut(source.qualifiers.as_mut().unwrap()).object_type_evidence = Some(evidence);
        let ((shared, output), work) = crate::instrumentation::measure_deterministic_work(|| {
            let shared = SharedPointerValue::import(&source);
            let output = shared.export().unwrap();
            (shared, output)
        });
        assert!(work <= 100, "size={size}, work={work}");
        let before = source
            .qualifiers
            .as_ref()
            .unwrap()
            .object_type_evidence
            .as_ref()
            .unwrap();
        let after = output
            .qualifiers
            .as_ref()
            .unwrap()
            .object_type_evidence
            .as_ref()
            .unwrap();
        assert!(before.premises.ptr_eq(&after.premises));
        assert_eq!(
            shared
                .node()
                .qualifiers
                .as_ref()
                .unwrap()
                .object_type_evidence
                .as_ref()
                .unwrap()
                .premises
                .len(),
            size
        );
    }
}

#[test]
fn complete_pointer_construction_retains_shared_extent_width_dags() {
    for size in [16, 64, 256] {
        let source = SharedPointerValue::import(&complete_source());
        let mut value = source.node().clone();
        let mut width =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(1000011));
        for _ in 0..size {
            width = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [width.clone(), width],
            );
        }
        Arc::make_mut(value.qualifiers.as_mut().unwrap())
            .extent
            .as_mut()
            .unwrap()
            .width = width.clone();
        let exports = KernelTermExport::machine_export_count();
        let (shared, work) =
            crate::instrumentation::measure_deterministic_work(|| SharedPointerValue::new(value));
        assert_eq!(work, 1);
        assert_eq!(
            &shared
                .node()
                .qualifiers
                .as_ref()
                .unwrap()
                .extent
                .as_ref()
                .unwrap()
                .width,
            &width
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}
