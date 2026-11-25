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
        let mut bounds = value.array.bounds().unwrap().clone();
        bounds.width = width.clone();
        value.array = value.array.with_bounds(Some(bounds));
        let exports = KernelTermExport::machine_export_count();
        let (shared, work) =
            crate::instrumentation::measure_deterministic_work(|| SharedPointer::new(value));
        assert_eq!(work, 1);
        assert_eq!(&shared.node().array.bounds().unwrap().width, &width);
        let equivalent = SharedPointer::new(shared.node().clone());
        let mut different = shared.node().clone();
        different.array = different.array.with_owner(None);
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

#[test]
fn pointer_storage_keys_hash_the_shared_bounds_width_once() {
    use std::hash::Hash;

    for depth in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = SharedPointer::import(&complete_source());
        let mut value = source.node().clone();
        let mut width =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(1000012));
        for _ in 0..depth {
            width = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [width.clone(), width],
            );
        }
        let mut bounds = value.array.bounds().unwrap().clone();
        bounds.width = width;
        value.array = value.array.with_bounds(Some(bounds));
        let root = KernelTerm::shared_pointer_value(SharedPointer::new(value));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::execution_value::storage_keys::pointer_for_root(&root)
                .hash(&mut std::collections::hash_map::DefaultHasher::new());
        });
        assert!(work <= 4 * depth + 64, "depth={depth}, work={work}");
        assert!(!root.has_cached_native_argument());
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}

#[test]
fn equal_pointer_payloads_intern_without_walking_children_or_live_pointers() {
    for size in [16, 64, 256] {
        let source = SharedPointer::import(&complete_source());
        let mut width =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(1000013));
        for _ in 0..size {
            width = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [width.clone(), width],
            );
        }
        // `size` unrelated live pointers, each with its own type.
        let live: Vec<_> = (0..size)
            .map(|index| {
                let mut value = source.node().clone();
                value.array = value.array.with_owner(Some(SharedAddress::import(
                    &Address::symbolic(Variable(1001000 + index as u64)),
                )));
                SharedPointer::new(value)
            })
            .collect();
        let mut value = source.node().clone();
        let mut bounds = value.array.bounds().unwrap().clone();
        bounds.width = width;
        value.array = value.array.with_bounds(Some(bounds));
        let first = SharedPointer::new(value.clone());
        let (second, work) =
            crate::instrumentation::measure_deterministic_work(|| SharedPointer::new(value));
        assert_eq!(work, 1, "size={size}");
        assert_eq!(first, second);
        let (terms_equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            KernelTerm::shared_pointer_value(first.clone())
                == KernelTerm::shared_pointer_value(second.clone())
        });
        assert!(terms_equal);
        assert!(work <= 8, "size={size}, work={work}");
        assert_eq!(live.len(), size);
    }
}
