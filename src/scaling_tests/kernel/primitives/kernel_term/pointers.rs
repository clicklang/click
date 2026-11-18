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
            let shared = SharedPointer::import(&source);
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
        let named = SharedPointer::import(&source);
        let (matches, work) = crate::instrumentation::measure_deterministic_work(|| {
            named.same_source_payload(&shared)
        });
        assert!(matches);
        assert_eq!(work, 1, "source matching must not walk {size} premises");
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
fn complete_pointer_construction_retains_shared_bounds_width_dags() {
    for size in [16, 64, 256] {
        let source = SharedPointer::import(&complete_source());
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
            .bounds
            .as_mut()
            .unwrap()
            .width = width.clone();
        let exports = KernelTermExport::machine_export_count();
        let (shared, work) =
            crate::instrumentation::measure_deterministic_work(|| SharedPointer::new(value));
        assert_eq!(work, 1);
        assert_eq!(
            &shared
                .node()
                .qualifiers
                .as_ref()
                .unwrap()
                .bounds
                .as_ref()
                .unwrap()
                .width,
            &width
        );
        let equivalent = SharedPointer::new(shared.node().clone());
        let mut different = shared.node().clone();
        Arc::make_mut(different.qualifiers.as_mut().unwrap()).constant = false;
        let different = SharedPointer::new(different);
        let (matches, work) = crate::instrumentation::measure_deterministic_work(|| {
            (
                shared.same_source_payload(&equivalent),
                shared.same_source_payload(&different),
            )
        });
        assert_eq!(matches, (true, false));
        assert_eq!(
            work, 2,
            "source matching must not walk the {size}-node width DAG"
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}
