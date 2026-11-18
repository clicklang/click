use super::*;

#[test]
fn address_construction_and_identity_do_not_walk_displacement_dags() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| SharedAddressBase::import(&AddressBase::Heap(i)))
            .collect::<Vec<_>>();
        let block = SharedAddressBase::import(&AddressBase::Symbolic(Variable(999001)));
        for size in [16, 64, 256] {
            let mut offset = KernelAddressOffset::Constant(0).into_shared().unwrap();
            for _ in 0..size {
                offset = KernelAddressOffset::Add([offset.clone(), offset])
                    .into_shared()
                    .unwrap();
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let a = SharedAddress::new(block.clone(), offset.clone());
                let b = SharedAddress::new(block.clone(), offset.clone());
                assert_eq!(a, b);
                let mut hash = std::collections::hash_map::DefaultHasher::new();
                a.hash(&mut hash);
                assert_eq!(a.node().offset, offset);
            });
            assert_eq!(work, 2, "size={size}, unrelated={unrelated}");
        }
    }
}

#[test]
fn block_import_charges_selected_bytes_not_unrelated_literal_bytes() {
    for size in [16, 64, 256] {
        let _unrelated = (0..size)
            .map(|i| {
                SharedAddressBase::import(&AddressBase::StringLiteral {
                    identity: StringLiteralId::new(format!("unrelated-{i}"), 0),
                    bytes: vec![0; size * 16],
                })
            })
            .collect::<Vec<_>>();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            SharedAddressBase::import(&AddressBase::Symbolic(Variable(999002)))
        });
        // Identifier atoms bypass the variable-sized payload interner.
        assert_eq!(work, 1);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            SharedAddressBase::import(&AddressBase::Concrete("x".repeat(size)))
        });
        assert_eq!(work, 9 + size);
    }
}

#[test]
fn named_pointer_admission_cost_is_independent_of_prior_imports() {
    for size in [16, 64, 256] {
        let block = AddressBase::Concrete("n".repeat(size));
        let mut retained = Vec::new();
        for _ in 0..3 {
            let (value, work) = crate::instrumentation::measure_deterministic_work(|| {
                SharedAddressBase::import_with_upkeep(&block, true)
            });
            assert_eq!(work, 9 + size);
            retained.push(value);
        }
        assert!(retained.windows(2).all(|pair| pair[0] == pair[1]));
    }
}

#[test]
fn raw_pointer_conditions_keep_shared_displacements_through_rewrites_and_transport() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut offset = KernelAddressOffset::Int32Scaled {
            value: KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(999701)),
            byte_width: 4,
        }
        .into_shared()
        .unwrap();
        for _ in 0..size {
            offset = KernelAddressOffset::Add([offset.clone(), offset])
                .into_shared()
                .unwrap();
        }
        let address = SharedAddress::new(
            SharedAddressBase::import(&AddressBase::Symbolic(Variable(999700))),
            offset.clone(),
        );
        let source = KernelTerm::pointer_equal_raw([address.clone(), address]);
        let nested = KernelTerm::boolean_equal_raw([
            source.clone(),
            KernelTerm::intern(KernelType::Bool, KernelTermNode::BoolLiteral(false)),
        ]);
        let exports = KernelTermExport::machine_export_count();
        let ((bits, pointers, transported), work) =
            crate::instrumentation::measure_deterministic_work(|| {
                let bits =
                    crate::kernel::reasoning::substitute_bitvector_variable_in_common_condition(
                        &source,
                        Variable(999702),
                        &MachineTerm::constant(1),
                    )
                    .unwrap();
                let pointers =
                    crate::kernel::reasoning::substitute_pointer_variable_in_common_condition(
                        &nested,
                        Variable(999700),
                        &Address::symbolic(Variable(999703)),
                    )
                    .unwrap();
                let transported = crate::kernel::memory_history::transport_framed_common_condition(
                    &source,
                    &crate::kernel::SymbolicMemory::new(),
                    None,
                )
                .unwrap();
                (bits, pointers, transported)
            });
        assert_eq!(bits, source);
        assert_eq!(transported, source);
        let KernelTermNode::BoolEqual { arguments } = pointers.node() else {
            panic!("Boolean equality")
        };
        let KernelTermNode::PointerEqual { arguments } = arguments[0].node() else {
            panic!("raw address equality")
        };
        assert_eq!(arguments[0].node().offset, offset);
        assert_eq!(
            arguments[0].node().base.native_atom(),
            &AddressBase::Symbolic(Variable(999703))
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work <= 100 * size + 1000, "size={size}, work={work}");
    }
}

#[test]
fn complete_pointer_conditions_keep_shared_domains_through_rewrites_and_observations() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut offset = KernelAddressOffset::Int32Scaled {
            value: KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(999801)),
            byte_width: 4,
        }
        .into_shared()
        .unwrap();
        for _ in 0..size {
            offset = KernelAddressOffset::Add([offset.clone(), offset])
                .into_shared()
                .unwrap();
        }
        let values = [999802, 999803].map(|variable| {
            let source = SharedPointer::import(&Pointer::new(
                Address::symbolic(Variable(variable)),
                ProgramType::Int32Pointer,
            ));
            let mut value = source.node().clone();
            value.address = SharedAddress::new(value.address.node().base.clone(), offset.clone());
            SharedPointer::new(value)
        });
        let root = KernelTerm::pointer_value_equal_raw(values.clone());
        let one = KernelTermImport::default()
            .machine(MachineIntegerType::Int32, &MachineTerm::constant(1));
        let zero = KernelTermImport::default()
            .machine(MachineIntegerType::Int32, &MachineTerm::constant(0));
        let exports = KernelTermExport::machine_export_count();
        let ((bits, pointers), work) = crate::instrumentation::measure_deterministic_work(|| {
            let bits = crate::kernel::reasoning::substitute_bitvector_variable_in_common_condition(
                &root,
                Variable(999809),
                &MachineTerm::constant(1),
            )
            .unwrap();
            let pointers =
                crate::kernel::reasoning::substitute_pointer_variable_in_common_condition(
                    &root,
                    Variable(999809),
                    &Address::null(),
                )
                .unwrap();
            assert_eq!(
                crate::kernel::memory_history::transport_framed_common_condition(
                    &root,
                    &crate::kernel::SymbolicMemory::new(),
                    None
                ),
                Some(root.clone())
            );
            let observed = SharedMachineIntegerTerm::observe_shared(
                MachineIntegerType::Int32,
                KernelTerm::machine_if_shared(
                    MachineIntegerType::Int32,
                    [root.clone(), one.clone(), zero.clone()],
                ),
            )
            .unwrap();
            let again = SharedMachineIntegerTerm::observe_shared(
                MachineIntegerType::Int32,
                KernelTerm::machine_if_shared(
                    MachineIntegerType::Int32,
                    [root.clone(), one.clone(), zero.clone()],
                ),
            )
            .unwrap();
            assert_eq!(observed, again);
            (bits, pointers)
        });
        assert_eq!(bits, root);
        let KernelTermNode::PointerValueEqual(pair) = pointers.node() else {
            panic!("complete pointer equality");
        };
        assert_eq!(pair.arguments()[0].node().address.node().offset, offset);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work <= 500 * size + 5000, "size={size}, work={work}");
    }
}
