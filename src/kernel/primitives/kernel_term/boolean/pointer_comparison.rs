//! Existing raw-address equality construction over retained address operands.
use super::*;

impl KernelTerm {
    pub(crate) fn pointer_equal_raw(arguments: [SharedPointerAddress; 2]) -> Self {
        Self::intern(KernelType::Bool, KernelTermNode::PointerEqual { arguments })
    }

    pub(crate) fn pointer_equal(arguments: [SharedPointerAddress; 2]) -> Self {
        let [a, b] = arguments.each_ref().map(|address| address.node());
        let left = a.block.native_atom();
        let right = b.block.native_atom();
        if left.proven_distinct(right) {
            return Self::intern(KernelType::Bool, KernelTermNode::BoolLiteral(false));
        }
        if left == right {
            let comparison = Self::pointer_offset_equal([a.offset.clone(), b.offset.clone()]);
            if let KernelTermNode::BoolLiteral(value) = comparison.node()
                && !(*value && matches!(left, PointerBlock::LoadedPointer(_)))
            {
                return comparison;
            }
        }
        Self::pointer_equal_raw(arguments)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn pointers() -> Vec<Pointer> {
        let memory =
            crate::kernel::intern_memory(crate::kernel::Memory::new().with_block("raw-pointer", 8));
        let mut values = vec![
            Pointer::null(),
            Pointer::symbolic(Variable(999001)),
            Pointer {
                block: PointerBlock::FunctionSymbolic(Variable(999001)),
                offset: PointerOffsetTerm::Constant(0),
            },
            Pointer {
                block: PointerBlock::ExternalObject(Variable(999001)),
                offset: PointerOffsetTerm::Constant(0),
            },
            crate::kernel::Memory::global_pointer("raw-pointer"),
            Pointer::loaded_value(
                &memory,
                &crate::kernel::Memory::global_pointer("raw-pointer"),
            ),
            Pointer::integer_address(MachineTerm::Variable(Variable(999002))),
            Pointer {
                block: PointerBlock::PureFunctionApplication(SharedPureApplication::intern(
                    "raw_pointer_call".into(),
                    vec![PureFunctionArgument::Value(ProgramValue::Int32(
                        MachineTerm::Variable(Variable(999002)),
                    ))],
                )),
                offset: PointerOffsetTerm::Constant(0),
            },
        ];
        let base = values.clone();
        for pointer in base {
            values.push(Pointer {
                block: pointer.block,
                offset: PointerOffsetTerm::Add(
                    Box::new(PointerOffsetTerm::Constant(0)),
                    Box::new(PointerOffsetTerm::scaled_int32_node(
                        MachineTerm::Variable(Variable(999002)),
                        4,
                    )),
                ),
            });
        }
        values
    }

    #[test]
    fn raw_pointer_condition_constructors_match_native_blocks_and_offsets() {
        let _session = crate::kernel::VerificationSession::enter();
        let values = pointers();
        for a in &values {
            for b in &values {
                let shared = [
                    SharedPointerAddress::import(a),
                    SharedPointerAddress::import(b),
                ];
                let expected = ConditionTerm::pointer_equal(a.clone(), b.clone());
                let actual = KernelTerm::pointer_equal(shared);
                assert_eq!(KernelTermExport::condition(&actual).unwrap(), expected);
                let raw = ConditionTerm::PointerEqual(Box::new(a.clone()), Box::new(b.clone()));
                let root = KernelTermImport::default().condition(&raw);
                assert!(matches!(root.node(), KernelTermNode::PointerEqual { .. }));
                assert_eq!(
                    format!("{:?}", KernelTermExport::condition(&root).unwrap()),
                    format!("{raw:?}")
                );
                assert!(
                    BooleanOperandView::Shared(&root)
                        .syntax_equal(BooleanOperandView::Native(&raw))
                );
            }
        }
    }

    #[test]
    fn raw_pointer_condition_substitutions_preserve_native_policy() {
        let _session = crate::kernel::VerificationSession::enter();
        let target = Pointer {
            block: PointerBlock::Symbolic(Variable(999010)),
            offset: PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Constant(1)),
                Box::new(PointerOffsetTerm::Constant(2)),
            ),
        };
        for pointer in pointers() {
            let source = ConditionTerm::PointerEqual(Box::new(pointer), Box::new(Pointer::null()));
            for source in [
                source.clone(),
                ConditionTerm::BoolEqual(
                    Box::new(source),
                    Box::new(ConditionTerm::Constant(false)),
                ),
            ] {
                let root = KernelTermImport::default().condition(&source);
                let bits = MachineTerm::constant(3);
                let expected = crate::kernel::reasoning::substitute_bitvector_variable_in_condition(
                    &source,
                    Variable(999002),
                    &bits,
                );
                let actual =
                    crate::kernel::reasoning::substitute_bitvector_variable_in_common_condition(
                        &root,
                        Variable(999002),
                        &bits,
                    )
                    .unwrap();
                assert_eq!(
                    format!("{:?}", KernelTermExport::condition(&actual).unwrap()),
                    format!("{expected:?}"),
                    "{source:?}"
                );
                let expected = crate::kernel::reasoning::substitute_pointer_variable_in_proposition(
                    &Proposition::ConditionIs(source.clone(), true),
                    Variable(999001),
                    &target,
                );
                let Proposition::ConditionIs(expected, true) = expected else {
                    panic!("condition")
                };
                let actual =
                    crate::kernel::reasoning::substitute_pointer_variable_in_common_condition(
                        &root,
                        Variable(999001),
                        &target,
                    )
                    .unwrap();
                assert_eq!(
                    format!("{:?}", KernelTermExport::condition(&actual).unwrap()),
                    format!("{expected:?}"),
                    "{source:?}"
                );
            }
        }
    }

    #[test]
    fn raw_pointer_condition_observations_use_semantic_call_identity() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        let _session = crate::kernel::VerificationSession::enter();
        let roots = [CScalarClass::Int, CScalarClass::Char].map(|class| {
            let block = PointerBlock::PureFunctionApplication(SharedPureApplication::intern(
                "raw_pointer_metadata".into(),
                vec![PureFunctionArgument::Value(ProgramValue::UInt64(
                    MachineTerm::PointerAddress(
                        Box::new(Pointer::symbolic(Variable(999020))),
                        AddressObjectClass::new(Some(CAccessClass::Scalar(class))),
                    ),
                ))],
            ));
            let source = ConditionTerm::PointerEqual(
                Box::new(Pointer {
                    block,
                    offset: PointerOffsetTerm::Constant(0),
                }),
                Box::new(Pointer::null()),
            );
            KernelTermImport::default().condition(&source)
        });
        assert_ne!(roots[0], roots[1]);
        assert!(
            BooleanOperandView::Shared(&roots[0])
                .syntax_equal(BooleanOperandView::Shared(&roots[1]))
        );
        let one = KernelTermImport::default()
            .machine(MachineIntegerType::Int32, &MachineTerm::constant(1));
        let zero = KernelTermImport::default()
            .machine(MachineIntegerType::Int32, &MachineTerm::constant(0));
        let observations = roots.map(|guard| {
            SharedMachineIntegerTerm::observe_shared(
                MachineIntegerType::Int32,
                KernelTerm::machine_if_shared(
                    MachineIntegerType::Int32,
                    [guard, one.clone(), zero.clone()],
                ),
            )
            .unwrap()
        });
        assert_eq!(observations[0], observations[1]);
    }
    #[test]
    fn raw_pointer_conditions_preserve_narrow_load_authority_and_wide_exact_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let before = crate::kernel::Memory::new()
            .with_block("offset-condition", 8)
            .with_block("offset-other", 4);
        let after = before.clone().store(
            crate::kernel::Memory::global_pointer("offset-other"),
            ProgramValue::Int32(MachineTerm::constant(1)),
        );
        let memory_a = crate::kernel::intern_memory(before);
        let memory_b = crate::kernel::intern_memory(after);
        for wide in [false, true] {
            let condition = |memory| {
                let value = MachineTerm::MemoryLoad(
                    memory,
                    Box::new(crate::kernel::Memory::global_pointer("offset-condition")),
                    if wide {
                        LoadKind::Bits64
                    } else {
                        LoadKind::Int32
                    },
                );
                let offset = if wide {
                    PointerOffsetTerm::scaled_int64_node(value, 8, false)
                } else {
                    PointerOffsetTerm::scaled_int32_node(value, 4)
                };
                ConditionTerm::PointerEqual(
                    Box::new(Pointer {
                        block: PointerBlock::Symbolic(Variable(999030)),
                        offset,
                    }),
                    Box::new(Pointer::null()),
                )
            };
            let a = condition(memory_a.clone());
            let b = condition(memory_b.clone());
            let ar = KernelTermImport::default().condition(&a);
            let br = KernelTermImport::default().condition(&b);
            for allowed in [false, true] {
                let loads = |_: &MachineTerm, _: &MachineTerm| allowed;
                let expected =
                    crate::kernel::assumptions::conditions_equal_with_load_atoms(&a, &b, &loads);
                assert_eq!(
                    crate::kernel::assumptions::boolean_operands_equal_with_load_atoms(
                        BooleanOperandView::Shared(&ar),
                        BooleanOperandView::Shared(&br),
                        &loads
                    ),
                    expected
                );
                assert_eq!(
                    crate::kernel::assumptions::boolean_operands_equal_with_load_atoms(
                        BooleanOperandView::Shared(&ar),
                        BooleanOperandView::Native(&b),
                        &loads
                    ),
                    expected
                );
                assert!(
                    crate::kernel::assumptions::boolean_operands_equal_with_load_atoms(
                        BooleanOperandView::Shared(&ar),
                        BooleanOperandView::Shared(&ar),
                        &loads
                    )
                );
            }
        }
    }
}
