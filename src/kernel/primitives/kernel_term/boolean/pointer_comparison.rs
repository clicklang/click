//! Existing raw-address equality construction over retained address operands.
use super::*;

impl SharedAddress {
    pub(in crate::kernel::primitives) fn equality_value(
        &self,
        other: &Self,
        constant: impl Fn(&SharedAddressOffset) -> Option<i64>,
    ) -> Option<bool> {
        let left = self.atom();
        let right = other.atom();
        if left.proven_distinct(right) {
            return Some(false);
        }
        if left != right {
            return None;
        }
        // Preserve reflexive comparisons of loaded pointers and slice data as
        // written evidence. The graph can still derive their offset equality.
        self.offset()
            .equality_value(other.offset(), constant)
            .filter(|value| {
                !(*value && matches!(left, AddressBase::Load(_) | AddressBase::SliceData(_)))
            })
    }
}

impl KernelTerm {
    pub(crate) fn address_equal_raw(arguments: [SharedAddress; 2]) -> Self {
        let block_payloads = arguments.each_ref().map(|a| a.atom().block_payload());
        Self::intern(
            KernelType::Bool,
            KernelTermNode::AddressEqual {
                arguments,
                block_payloads,
            },
        )
    }

    pub(crate) fn address_equal(arguments: [SharedAddress; 2]) -> Self {
        Self::address_equal_with(arguments, SharedAddressOffset::as_const)
    }

    pub(in crate::kernel::primitives) fn address_equal_with(
        arguments: [SharedAddress; 2],
        constant: impl Fn(&SharedAddressOffset) -> Option<i64>,
    ) -> Self {
        let [a, b] = &arguments;
        match a.equality_value(b, constant) {
            Some(value) => Self::boolean_literal(value),
            None => Self::address_equal_raw(arguments),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn pointers() -> Vec<Address> {
        let memory = crate::kernel::intern_memory(
            crate::kernel::SymbolicMemory::new().with_block("raw-pointer", 8),
        );
        let mut values = vec![
            Address::null(),
            Address::symbolic(Variable(999001)),
            Address::new(
                AddressBase::FunctionSymbolic(Variable(999001)),
                AddressOffset::constant(0),
            ),
            Address::new(
                AddressBase::ExternalObject(Variable(999001)),
                AddressOffset::constant(0),
            ),
            crate::kernel::SymbolicMemory::global_pointer("raw-pointer"),
            Address::loaded_value(
                &memory,
                &crate::kernel::SymbolicMemory::global_pointer("raw-pointer"),
            ),
            Address::from_integer_address(OldMachineTerm::Variable(Variable(999002))),
            Address::new(
                AddressBase::PureFunctionApplication(SharedPureApplication::intern(
                    "raw_pointer_call".into(),
                    vec![PureFunctionArgument::Value(ProgramValue::Int32(
                        OldMachineTerm::Variable(Variable(999002)),
                    ))],
                )),
                AddressOffset::constant(0),
            ),
        ];
        let base = values.clone();
        for pointer in base {
            values.push(pointer.with_offset(AddressOffset::raw_add(
                AddressOffset::constant(0),
                AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(999002)), 4),
            )));
        }
        values
    }

    #[test]
    fn raw_pointer_condition_constructors_match_native_blocks_and_offsets() {
        let _session = crate::kernel::VerificationSession::enter();
        let values = pointers();
        for a in &values {
            for b in &values {
                let shared = [a.shared().clone(), b.shared().clone()];
                let expected = OldConditionTerm::address_equal(a.clone(), b.clone());
                let actual = KernelTerm::address_equal(shared);
                assert_eq!(KernelTermExport::condition(&actual).unwrap(), expected);
                let raw = OldConditionTerm::AddressEqual(Box::new(a.clone()), Box::new(b.clone()));
                let root = KernelTermImport::default().condition(&raw);
                assert!(matches!(root.node(), KernelTermNode::AddressEqual { .. }));
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
        let target = Address::new(
            AddressBase::Symbolic(Variable(999010)),
            AddressOffset::raw_add(AddressOffset::constant(1), AddressOffset::constant(2)),
        );
        for pointer in pointers() {
            let source =
                OldConditionTerm::AddressEqual(Box::new(pointer), Box::new(Address::null()));
            for source in [
                source.clone(),
                OldConditionTerm::BoolEqual(
                    Box::new(source),
                    Box::new(OldConditionTerm::Constant(false)),
                ),
            ] {
                let root = KernelTermImport::default().condition(&source);
                let bits = OldMachineTerm::constant(3);
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
                    &Proposition::condition_is(source.clone(), true),
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
            let block = AddressBase::PureFunctionApplication(SharedPureApplication::intern(
                "raw_pointer_metadata".into(),
                vec![PureFunctionArgument::Value(ProgramValue::UInt64(
                    OldMachineTerm::IntegerAddress(
                        Box::new(Address::symbolic(Variable(999020))),
                        AddressObjectClass::new(Some(CAccessClass::Scalar(class))),
                    ),
                ))],
            ));
            let source = OldConditionTerm::AddressEqual(
                Box::new(Address::new(block, AddressOffset::constant(0))),
                Box::new(Address::null()),
            );
            KernelTermImport::default().condition(&source)
        });
        assert_ne!(roots[0], roots[1]);
        assert!(
            BooleanOperandView::Shared(&roots[0])
                .syntax_equal(BooleanOperandView::Shared(&roots[1]))
        );
        let one = KernelTermImport::default()
            .machine(MachineIntegerType::Int32, &OldMachineTerm::constant(1));
        let zero = KernelTermImport::default()
            .machine(MachineIntegerType::Int32, &OldMachineTerm::constant(0));
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
        let before = crate::kernel::SymbolicMemory::new()
            .with_block("offset-condition", 8)
            .with_block("offset-other", 4);
        let after = before.clone().store(
            crate::kernel::SymbolicMemory::global_pointer("offset-other"),
            ProgramValue::Int32(OldMachineTerm::constant(1)),
        );
        let memory_a = crate::kernel::intern_memory(before);
        let memory_b = crate::kernel::intern_memory(after);
        for wide in [false, true] {
            let condition = |memory| {
                let value = OldMachineTerm::read_named(
                    memory,
                    Box::new(crate::kernel::SymbolicMemory::global_pointer(
                        "offset-condition",
                    )),
                    if wide {
                        LoadKind::Bits64
                    } else {
                        LoadKind::Int32
                    },
                );
                let offset = if wide {
                    AddressOffset::scaled_int64_node(value, 8, false)
                } else {
                    AddressOffset::scaled_int32_node(value, 4)
                };
                OldConditionTerm::AddressEqual(
                    Box::new(Address::new(
                        AddressBase::Symbolic(Variable(999030)),
                        offset,
                    )),
                    Box::new(Address::null()),
                )
            };
            let a = condition(ProgramPoint::at(&memory_a));
            let b = condition(ProgramPoint::at(&memory_b));
            let ar = KernelTermImport::default().condition(&a);
            let br = KernelTermImport::default().condition(&b);
            for allowed in [false, true] {
                let loads = |_: &OldMachineTerm, _: &OldMachineTerm| allowed;
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
