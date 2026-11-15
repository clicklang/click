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

#[test]
fn float_arithmetic_retains_dag_operands_without_exporting_prefixes() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            let mut root =
                KernelTerm::variable(KernelType::Program(format.program_type()), Variable(999931));
            for _ in 0..size {
                let child = root.clone();
                let (next, work) = crate::instrumentation::measure_deterministic_work(|| {
                    KernelTerm::float_binary(
                        format,
                        FloatBinaryOperator::Add,
                        [root.clone(), root.clone()],
                    )
                    .unwrap()
                });
                assert!(work <= 4, "size={size}, work={work}");
                assert_eq!(next.children(), &[child.clone(), child]);
                assert!(next.0.machine_leaf.0.get().is_none());
                root = next;
            }
        }
    }
}

#[test]
fn float_arithmetic_native_boundaries_walk_only_explicit_output_size() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            let mut native = MachineTerm::Variable(Variable(999932));
            for _ in 0..size {
                native = match format {
                    KernelFloatType::Float32 => MachineTerm::Float32Negate(Box::new(native)),
                    KernelFloatType::Float64 => MachineTerm::Float64Negate(Box::new(native)),
                };
            }
            let (root, import_work) = crate::instrumentation::measure_deterministic_work(|| {
                KernelTermImport::default().float(format, &native)
            });
            let (exported, export_work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    KernelTermExport::float(&root).unwrap()
                });
            assert_eq!(exported, format.value(native));
            assert!(
                import_work <= 4 * size + 16,
                "size={size}, work={import_work}"
            );
            assert!(
                export_work <= 4 * size + 16,
                "size={size}, work={export_work}"
            );
            assert!(root.0.machine_leaf.0.get().is_none());
        }
    }
}

#[test]
fn conversion_rebuild_does_not_scan_symbolic_operand_prefixes() {
    for size in [16, 64, 256] {
        let mut operand = MachineTerm::Variable(Variable(999951));
        for _ in 0..size {
            operand = MachineTerm::Float32Negate(Box::new(operand));
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            MachineTerm::rebuild_pure_application("c_float32_to_float64".into(), vec![operand])
        });
        assert!(matches!(
            result,
            MachineTerm::PureFunctionApplication { .. }
        ));
        assert!(work <= 1, "size={size}: work={work}");
    }
}

#[test]
fn float_conversion_chains_preserve_shared_operands_without_exports() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut root =
            KernelTerm::variable(KernelType::Program(ProgramType::Float32), Variable(999962));
        let mut source = ProgramType::Float32;
        let exports = KernelTermExport::machine_export_count();
        for _ in 0..size {
            let target = if source == ProgramType::Float32 {
                KernelFloatType::Float64
            } else {
                KernelFloatType::Float32
            };
            let (next, work) = crate::instrumentation::measure_deterministic_work(|| {
                KernelTerm::float_convert(target, source, root.clone()).unwrap()
            });
            assert!(work <= 4, "size={size}: work={work}");
            assert_eq!(next.children()[0].id(), root.id());
            root = next;
            source = target.program_type();
        }
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        let (native, export_work) = crate::instrumentation::measure_deterministic_work(|| {
            KernelTermExport::float(&root).unwrap()
        });
        assert!(export_work <= 3 * size + 4, "{size}: {export_work}");
        let (again, import_work) = crate::instrumentation::measure_deterministic_work(|| {
            KernelTermImport::default().argument(&PureFunctionArgument::Value(native))
        });
        assert_eq!(again, root);
        assert!(import_work <= 5 * size + 8, "{size}: {import_work}");
    }
}
