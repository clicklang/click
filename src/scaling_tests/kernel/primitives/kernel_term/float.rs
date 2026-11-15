use super::*;

#[test]
fn float_atom_views_do_constant_work_beside_growing_arenas() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let unrelated = (0..size)
            .map(|index| KernelTerm::variable(KernelType::Integer, Variable(999900 + index)))
            .collect::<Vec<_>>();
        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            let native = match format {
                KernelFloatType::Float32 => MachineTerm::constant(0x7fc00001),
                KernelFloatType::Float64 => MachineTerm::uint64_constant(0x7ff8000000000001),
            };
            let exports = KernelTermExport::machine_export_count();
            let (root, work) = crate::instrumentation::measure_deterministic_work(|| {
                let root = KernelTermImport::default().float(format, &native);
                let view = FloatOperandView::from_shared(&root).unwrap();
                assert_eq!(view.format(), format);
                assert!(view.literal().is_some());
                assert_eq!(view.variable(), None);
                assert_eq!(view.native_compat(), Some(&native));
                root
            });
            assert!(work <= 4, "size={size}, work={work}");
            assert!(root.children().is_empty());
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert_eq!(unrelated.len(), size as usize);
        }
    }
}

#[test]
fn float_read_construction_keeps_growing_shared_addresses_and_snapshots() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut index =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(999920));
        let mut memory = Memory::new();
        for i in 0..size {
            index = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [index.clone(), index],
            );
            memory = memory.with_block(format!("float-unrelated-{i}"), 8);
        }
        let memory = intern_memory(memory);
        let address = SharedPointerAddress::new(
            SharedPointerBlock::import(&PointerBlock::Symbolic(Variable(999921))),
            KernelPointerOffset::Int32Scaled {
                value: index,
                byte_width: 4,
            }
            .into_shared()
            .unwrap(),
        );
        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let root = KernelTerm::float_read(format, memory.clone(), address.clone());
                let KernelTermNode::FloatRead(read) = root.node() else {
                    panic!("read")
                };
                assert_eq!(read.parts().0.arena_id(), memory.arena_id());
                assert_eq!(read.parts().1, &address);
                assert_eq!(
                    root,
                    KernelTerm::float_read(format, memory.clone(), address.clone())
                );
            });
            assert!(work <= 16, "size={size}, work={work}");
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
}
