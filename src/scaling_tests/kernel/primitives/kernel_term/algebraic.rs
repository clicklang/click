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

#[test]
fn algebraic_match_argument_imports_visit_native_prefixes_once() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = KernelMatch::test_scrutinee(vec![]);
        let mut source = variable.clone();
        for _ in 0..size {
            source = AlgebraicTerm {
                algebraic_type: variable.algebraic_type.clone(),
                node: AlgebraicTermNode::Match {
                    scrutinee: Box::new(variable.clone()),
                    arms: vec![AlgebraicResultMatchArm {
                        variant: "Arm".into(),
                        bindings: vec![],
                        binding_names: Default::default(),
                        body: source,
                    }],
                },
            };
        }
        let exports = KernelTermExport::algebraic_export_count();
        let (root, work) = crate::instrumentation::measure_deterministic_work(|| {
            KernelTermImport::default().algebraic(&source)
        });
        assert!(work <= 20 * size + 100, "size={size} work={work}");
        assert_eq!(KernelTermExport::algebraic_export_count(), exports);
        assert_eq!(
            KernelTermExport::default().algebraic(&root).unwrap(),
            source
        );
    }
}

#[test]
fn algebraic_conditional_prefixes_import_and_export_linearly() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let leaf = KernelMatch::test_scrutinee(vec![]);
        let mut source = leaf.clone();
        for _ in 0..size {
            source = AlgebraicTerm {
                algebraic_type: leaf.algebraic_type.clone(),
                node: AlgebraicTermNode::If {
                    condition: Box::new(ConditionTerm::integer_equal(
                        IntegerTerm::var(Variable(999723)),
                        IntegerTerm::constant_i64(0),
                    )),
                    then_term: Box::new(source),
                    else_term: Box::new(leaf.clone()),
                },
            };
        }
        let exports = KernelTermExport::algebraic_export_count();
        let (root, work) = crate::instrumentation::measure_deterministic_work(|| {
            KernelTermImport::default().algebraic(&source)
        });
        assert!(work <= 40 * size + 100, "size={size} work={work}");
        assert_eq!(KernelTermExport::algebraic_export_count(), exports);
        let (native, work) = crate::instrumentation::measure_deterministic_work(|| {
            KernelTermExport::default().algebraic(&root).unwrap()
        });
        assert_eq!(native, source);
        assert!(work <= 40 * size + 100, "size={size} work={work}");
    }
}

#[test]
fn algebraic_read_construction_keeps_growing_shared_addresses_without_exports() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut index =
            KernelTerm::variable(KernelType::Program(format.program_type()), Variable(999747));
        for _ in 0..size {
            index = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [index.clone(), index],
            );
        }
        let pointer = Address {
            base: AddressBase::Symbolic(Variable(999748)),
            offset: AddressOffset::Int32Scaled {
                value: SharedMachineIntegerTerm::from_shared(format, index).unwrap(),
                byte_width: 4,
            },
        };
        let address = SharedAddress::import(&pointer);
        let ty = TypeParameterName::intern("ReadScaleT").algebraic_type();
        let memory = intern_memory(SymbolicMemory::new());
        let exports = KernelTermExport::machine_export_count();
        let (root, work) = crate::instrumentation::measure_deterministic_work(|| {
            KernelTerm::algebraic_read(
                ty.clone(),
                crate::kernel::ProgramPoint::at(&memory),
                address.clone(),
            )
        });
        let KernelTermNode::AlgebraicRead(read) = root.node() else {
            panic!("shared read")
        };
        assert_eq!(read.parts().1, &address);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work <= 8, "size={size} work={work}");
    }
}
