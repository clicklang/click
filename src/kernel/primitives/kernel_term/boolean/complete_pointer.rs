//! Complete pointer conditions retain producer payloads separately from their
//! observation identity. Qualifiers and evidence are never erased in producers.
use super::*;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct PointerIdentity {
    address: SharedAddress,
    provenance: SharedAddress,
    program_type: ProgramType,
    volatile: bool,
    bounds_known: bool,
    bounds_owner: Option<SharedAddress>,
    bounds: Option<(SharedAddress, KernelTerm)>,
}

#[derive(Clone, Debug)]
pub struct KernelPointerEquality {
    arguments: [SharedPointerValue; 2],
    observation: Option<Arc<[PointerIdentity; 2]>>,
}
impl PartialEq for KernelPointerEquality {
    fn eq(&self, other: &Self) -> bool {
        match (&self.observation, &other.observation) {
            (Some(a), Some(b)) => a == b,
            (None, None) => self.arguments == other.arguments,
            _ => false,
        }
    }
}
impl Eq for KernelPointerEquality {}
impl Hash for KernelPointerEquality {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.observation.is_some().hash(state);
        if let Some(identity) = &self.observation {
            identity.hash(state);
        } else {
            self.arguments.hash(state);
        }
    }
}
impl KernelPointerEquality {
    pub(crate) fn arguments(&self) -> &[SharedPointerValue; 2] {
        &self.arguments
    }
    pub(crate) fn observe(
        &self,
        mut address: impl FnMut(&SharedAddress) -> SharedAddress,
        mut numeric: impl FnMut(&KernelTerm) -> KernelTerm,
    ) -> Self {
        let observation = self.arguments.each_ref().map(|value| {
            let p = value.node();
            let q = p.qualifiers.as_ref();
            let known = q.is_some_and(|q| q.bounds_known);
            PointerIdentity {
                address: address(&p.address),
                provenance: address(&p.provenance),
                program_type: p.program_type,
                volatile: q.is_some_and(|q| q.volatile),
                bounds_known: known,
                bounds_owner: if known {
                    None
                } else {
                    p.bounds_owner.as_ref().map(&mut address)
                },
                bounds: q
                    .and_then(|q| q.bounds.as_ref())
                    .map(|e| (address(&e.start), numeric(&e.width))),
            }
        });
        Self {
            arguments: self.arguments.clone(),
            observation: Some(Arc::new(observation)),
        }
    }
}

impl SharedPointerValue {
    pub(crate) fn condition_syntax_equal(&self, other: &Self) -> bool {
        if self == other {
            return true;
        }
        let (a, b) = (self.node(), other.node());
        let (aq, bq) = (a.qualifiers.as_ref(), b.qualifiers.as_ref());
        let known = aq.is_some_and(|q| q.bounds_known);
        a.program_type == b.program_type
            && aq.is_some_and(|q| q.volatile) == bq.is_some_and(|q| q.volatile)
            && known == bq.is_some_and(|q| q.bounds_known)
            && a.address.syntax_equal(&b.address)
            && a.provenance.syntax_equal(&b.provenance)
            && (known
                || match (&a.bounds_owner, &b.bounds_owner) {
                    (None, None) => true,
                    (Some(a), Some(b)) => a.syntax_equal(b),
                    _ => false,
                })
            && self.condition_bounds_equal(other)
    }
    pub(crate) fn condition_bounds_equal(&self, other: &Self) -> bool {
        match (
            self.node()
                .qualifiers
                .as_ref()
                .and_then(|q| q.bounds.as_ref()),
            other
                .node()
                .qualifiers
                .as_ref()
                .and_then(|q| q.bounds.as_ref()),
        ) {
            (None, None) => true,
            (Some(a), Some(b)) => {
                a.start.syntax_equal(&b.start)
                    && crate::kernel::machine_operand_syntax_cmp(
                        MachineOperandView::Shared(&a.width),
                        MachineOperandView::Shared(&b.width),
                    )
                    .is_eq()
            }
            _ => false,
        }
    }
    /// Native map_pointers policy: addresses change, bounds width does not.
    pub(crate) fn map_condition_addresses<E>(
        &self,
        mut map: impl FnMut(&SharedAddress) -> Result<SharedAddress, E>,
    ) -> Result<Self, E> {
        let mut p = self.node().clone();
        p.address = map(&p.address)?;
        p.provenance = map(&p.provenance)?;
        p.bounds_owner = p.bounds_owner.as_ref().map(&mut map).transpose()?;
        if let Some(q) = &mut p.qualifiers
            && let Some(e) = &q.bounds
        {
            let start = map(&e.start)?;
            Arc::make_mut(q).bounds.as_mut().unwrap().start = start;
        }
        let result = Self::new(p);
        Ok(if self.same_source_payload(&result) {
            self.clone()
        } else {
            result
        })
    }
}
impl KernelTerm {
    pub(crate) fn pointer_value_equal_raw(arguments: [SharedPointerValue; 2]) -> Self {
        Self::intern(
            KernelType::Bool,
            KernelTermNode::PointerValueEqual(KernelPointerEquality {
                arguments,
                observation: None,
            }),
        )
    }
}

impl KernelTerm {
    pub(crate) fn pointer_value_equal(arguments: [SharedPointerValue; 2]) -> Self {
        let [left, right] = arguments.each_ref();
        let (a, b) = (left.node(), right.node());
        let (aq, bq) = (a.qualifiers.as_ref(), b.qualifiers.as_ref());
        let known = aq.is_some_and(|q| q.bounds_known);
        let same_domain = a.provenance.syntax_equal(&b.provenance)
            && left.condition_bounds_equal(right)
            && known == bq.is_some_and(|q| q.bounds_known)
            && (known
                || match (&a.bounds_owner, &b.bounds_owner) {
                    (None, None) => true,
                    (Some(a), Some(b)) => a.syntax_equal(b),
                    _ => false,
                });
        if same_domain
            || (matches!(a.program_type, ProgramType::FunctionPointer(_))
                && matches!(b.program_type, ProgramType::FunctionPointer(_)))
        {
            fn bits(address: &SharedAddress) -> Option<&MachineTerm> {
                if matches!(
                    address.node().offset.node(),
                    KernelAddressOffset::Constant(0)
                ) && let AddressBase::PureFunctionApplication(call) =
                    address.node().base.native_atom()
                {
                    call.integer_address_bits()
                } else {
                    None
                }
            }
            if bits(&a.address).is_some() || bits(&b.address).is_some() {
                let numeric = |address: &SharedAddress| {
                    if let Some(bits) = bits(address) {
                        return KernelTermImport::default()
                            .machine(MachineIntegerType::UInt64, bits);
                    }
                    if address.syntax_equal(&SharedAddress::import(&Address::null())) {
                        return KernelTermImport::default()
                            .machine(MachineIntegerType::UInt64, &MachineTerm::uint64_constant(0));
                    }
                    Self::shared_pointer_address_observation(
                        MachineIntegerType::UInt64,
                        address.clone(),
                        AddressObjectClass::NONE,
                    )
                };
                return Self::boolean_comparison(
                    MachineIntegerType::UInt64,
                    CompareRelation::Equal,
                    [numeric(&a.address), numeric(&b.address)],
                );
            }
            return Self::pointer_equal([a.address.clone(), b.address.clone()]);
        }
        Self::pointer_value_equal_raw(arguments.map(|value| {
            let p = value.node();
            value.with_binding_type_and_qualifiers(
                p.program_type,
                p.qualifiers.as_ref().is_some_and(|q| q.volatile),
                false,
            )
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn values() -> Vec<Pointer> {
        let mut values = Vec::new();
        for pointer in [
            Address::symbolic(Variable(999101)),
            Address::null(),
            Address::integer_address(MachineTerm::Variable(Variable(999102))),
            Address {
                base: AddressBase::ExternalObject(Variable(999101)),
                offset: AddressOffset::Constant(0),
            },
        ] {
            let raw = Pointer::new(pointer, ProgramType::Int32Pointer);
            values.push(raw.clone());
            values.push(raw.clone().with_pointee_constant(true));
            values.push(raw.clone().with_pointee_volatile(true));
            values.push(raw.clone().with_root_bounds());
            values.push(raw.clone().with_bounds(Some(SubobjectBounds {
                start: Address::symbolic(Variable(999101)),
                width: MachineTerm::Variable(Variable(999102)),
            })));
            values.push(
                raw.clone()
                    .with_provenance(Arc::new(Address::symbolic(Variable(999103)))),
            );
            values.push(raw.clone().with_address(Address {
                base: raw.base.clone(),
                offset: AddressOffset::Add(
                    Box::new(AddressOffset::Constant(0)),
                    Box::new(AddressOffset::scaled_int32_node(
                        MachineTerm::Variable(Variable(999102)),
                        4,
                    )),
                ),
            }));
        }
        values.push(Pointer::new(
            Address {
                base: AddressBase::FunctionSymbolic(Variable(999101)),
                offset: AddressOffset::Constant(0),
            },
            ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED),
        ));
        values.push(Pointer::new(
            Address::symbolic(Variable(999101)),
            ProgramType::VoidPointer,
        ));
        values
    }
    #[test]
    fn complete_pointer_conditions_preserve_native_identity_and_construction() {
        let _session = crate::kernel::VerificationSession::enter();
        let values = values();
        for a in &values {
            for b in &values {
                let shared = [SharedPointerValue::import(a), SharedPointerValue::import(b)];
                assert_eq!(shared[0].condition_syntax_equal(&shared[1]), a == b);
                let expected = ConditionTerm::pointer_value_equal(a.clone(), b.clone());
                let root = KernelTerm::pointer_value_equal(shared);
                assert_eq!(
                    format!("{:?}", KernelTermExport::condition(&root).unwrap()),
                    format!("{expected:?}")
                );
                let native =
                    ConditionTerm::PointerValueEqual(Box::new(a.clone()), Box::new(b.clone()));
                let root = KernelTermImport::default().condition(&native);
                assert!(matches!(root.node(), KernelTermNode::PointerValueEqual(_)));
                assert_eq!(
                    format!("{:?}", KernelTermExport::condition(&root).unwrap()),
                    format!("{native:?}")
                );
            }
        }
    }
    #[test]
    fn complete_pointer_conditions_preserve_substitution_domains() {
        let _session = crate::kernel::VerificationSession::enter();
        for value in values() {
            for to in [
                Address::null(),
                Address::symbolic(Variable(999110)),
                Address {
                    base: AddressBase::Symbolic(Variable(999110)),
                    offset: AddressOffset::Add(
                        Box::new(AddressOffset::Constant(1)),
                        Box::new(AddressOffset::Constant(2)),
                    ),
                },
            ] {
                let source = ConditionTerm::PointerValueEqual(
                    Box::new(value.clone()),
                    Box::new(Pointer::new(
                        Address::symbolic(Variable(999111)),
                        ProgramType::Int32Pointer,
                    )),
                );
                for source in [
                    source.clone(),
                    ConditionTerm::BoolEqual(
                        Box::new(source),
                        Box::new(ConditionTerm::Constant(false)),
                    ),
                ] {
                    let root = KernelTermImport::default().condition(&source);
                    let bits = MachineTerm::constant(3);
                    let expected =
                        crate::kernel::reasoning::substitute_bitvector_variable_in_condition(
                            &source,
                            Variable(999102),
                            &bits,
                        );
                    let actual = crate::kernel::reasoning::substitute_bitvector_variable_in_common_condition(&root,Variable(999102),&bits).unwrap();
                    assert_eq!(
                        format!("{:?}", KernelTermExport::condition(&actual).unwrap()),
                        format!("{expected:?}"),
                        "bits {source:?}"
                    );
                    let expected =
                        crate::kernel::reasoning::substitute_pointer_variable_in_proposition(
                            &Proposition::ConditionIs(source.clone(), true),
                            Variable(999101),
                            &to,
                        );
                    let Proposition::ConditionIs(expected, true) = expected else {
                        panic!("condition");
                    };
                    let actual =
                        crate::kernel::reasoning::substitute_pointer_variable_in_common_condition(
                            &root,
                            Variable(999101),
                            &to,
                        )
                        .unwrap();
                    assert_eq!(
                        format!("{:?}", KernelTermExport::condition(&actual).unwrap()),
                        format!("{expected:?}"),
                        "pointer {source:?}, target {to:?}"
                    );
                }
            }
        }
    }
    #[test]
    fn complete_pointer_conditions_observe_semantic_identity_without_erasing_producers() {
        let _session = crate::kernel::VerificationSession::enter();
        let value = Pointer::new(
            Address::symbolic(Variable(999120)),
            ProgramType::Int32Pointer,
        );
        let roots = [value.clone(), value.with_pointee_constant(true)].map(|value| {
            KernelTermImport::default().condition(&ConditionTerm::PointerValueEqual(
                Box::new(value),
                Box::new(Pointer::new(Address::null(), ProgramType::Int32Pointer)),
            ))
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
        let observed = roots.map(|guard| {
            SharedMachineIntegerTerm::observe_shared(
                MachineIntegerType::Int32,
                KernelTerm::machine_if_shared(
                    MachineIntegerType::Int32,
                    [guard, one.clone(), zero.clone()],
                ),
            )
            .unwrap()
        });
        assert_eq!(observed[0], observed[1]);
    }
    #[test]
    fn complete_pointer_conditions_observation_keys_match_native_value_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let values = values();
        let one = KernelTermImport::default()
            .machine(MachineIntegerType::Int32, &MachineTerm::constant(1));
        let zero = KernelTermImport::default()
            .machine(MachineIntegerType::Int32, &MachineTerm::constant(0));
        let observed: Vec<_> = values
            .iter()
            .map(|value| {
                let guard =
                    KernelTermImport::default().condition(&ConditionTerm::PointerValueEqual(
                        Box::new(value.clone()),
                        Box::new(Pointer::new(Address::null(), ProgramType::Int32Pointer)),
                    ));
                SharedMachineIntegerTerm::observe_shared(
                    MachineIntegerType::Int32,
                    KernelTerm::machine_if_shared(
                        MachineIntegerType::Int32,
                        [guard, one.clone(), zero.clone()],
                    ),
                )
                .unwrap()
            })
            .collect();
        for (i, a) in values.iter().enumerate() {
            for (j, b) in values.iter().enumerate() {
                assert_eq!(observed[i] == observed[j], a == b, "{a:?} / {b:?}");
            }
        }
    }
    #[test]
    fn complete_pointer_conditions_keep_exact_only_load_authority() {
        let _session = crate::kernel::VerificationSession::enter();
        let before = crate::kernel::Memory::new()
            .with_block("complete-read", 4)
            .with_block("complete-other", 4);
        let after = before.clone().store(
            crate::kernel::Memory::global_pointer("complete-other"),
            ProgramValue::Int32(MachineTerm::constant(1)),
        );
        let roots = [before, after].map(|memory| {
            let pointer = Address {
                base: AddressBase::Symbolic(Variable(999130)),
                offset: AddressOffset::scaled_int32_node(
                    MachineTerm::MemoryLoad(
                        ProgramPoint::at(&(crate::kernel::intern_memory(memory))),
                        Box::new(crate::kernel::Memory::global_pointer("complete-read")),
                        LoadKind::Int32,
                    ),
                    4,
                ),
            };
            KernelTermImport::default().condition(&ConditionTerm::PointerValueEqual(
                Box::new(Pointer::new(pointer, ProgramType::Int32Pointer)),
                Box::new(Pointer::new(Address::null(), ProgramType::Int32Pointer)),
            ))
        });
        for allowed in [false, true] {
            let loads = |_: &MachineTerm, _: &MachineTerm| allowed;
            assert!(
                !crate::kernel::assumptions::boolean_operands_equal_with_load_atoms(
                    BooleanOperandView::Shared(&roots[0]),
                    BooleanOperandView::Shared(&roots[1]),
                    &loads
                )
            );
            assert!(
                crate::kernel::assumptions::boolean_operands_equal_with_load_atoms(
                    BooleanOperandView::Shared(&roots[0]),
                    BooleanOperandView::Shared(&roots[0]),
                    &loads
                )
            );
        }
    }
}
