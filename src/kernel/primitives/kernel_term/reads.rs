//! Exact read terms at the native/shared boundary. This does not choose a
//! memory version, follow an alias, or read a stored value.
use super::*;

#[derive(Clone, Debug)]
pub struct KernelMemoryRead {
    point: ProgramPoint,
    address: SharedAddress,
    observation: Option<SharedAddress>,
}
impl PartialEq for KernelMemoryRead {
    fn eq(&self, other: &Self) -> bool {
        match (&self.observation, &other.observation) {
            (None, None) => {
                self.point.read_key() == other.point.read_key() && self.address == other.address
            }
            (Some(a), Some(b)) => self.point == other.point && a == b,
            _ => false,
        }
    }
}
impl Eq for KernelMemoryRead {}
impl Hash for KernelMemoryRead {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.observation.is_some().hash(state);
        if let Some(address) = &self.observation {
            self.point.hash(state);
            address.hash(state);
        } else {
            self.point.read_key().hash(state);
            self.address.hash(state);
        }
    }
}
impl KernelMemoryRead {
    pub(crate) fn new(point: ProgramPoint, address: SharedAddress) -> Self {
        Self {
            point,
            address,
            observation: None,
        }
    }
    pub(crate) fn parts(&self) -> (&ProgramPoint, &SharedAddress) {
        (&self.point, &self.address)
    }
    pub(crate) fn observe(&self, address: SharedAddress) -> Self {
        Self {
            point: self.point.clone(),
            address: self.address.clone(),
            observation: Some(address),
        }
    }
}

impl KernelTermImport {
    pub(super) fn scalar_read(
        &mut self,
        format: MachineIntegerType,
        value: &MachineTerm,
    ) -> Option<KernelTerm> {
        match value {
            MachineTerm::MemoryLoad(point, address, kind) => {
                KernelTerm::scalar_read_descriptor(format, point, address, *kind)
            }
            // Exact field carriers retain the producer's written name. A
            // registered name and its structural read have different native
            // reader scopes and must not share a selected output slot.
            MachineTerm::Variable(variable)
                if !self.exact_field_inputs && crate::kernel::eval::is_load_variable(variable) =>
            {
                self.machine_input_requires_export = true;
                crate::kernel::eval::registered_scalar_read_term(variable, format)
            }
            _ => None,
        }
    }
}

impl KernelTerm {
    /// Retain a pointer result only when its producer already retained a read
    /// definition. This reads term metadata, never hypotheses or stored values.
    pub(crate) fn retained_pointer_read(value: &OldPointer) -> Option<Self> {
        // Later arithmetic and ordinary pointer values belong to their own
        // producer slices. Do not clone or hash a growing displacement merely
        // to ask whether it is an undisplaced read atom.
        if !matches!(value.address().offset, AddressOffset::Constant(0))
            || !matches!(
                value.address().base,
                AddressBase::Load(_) | AddressBase::FunctionSymbolic(_)
            )
        {
            return None;
        }
        let MachineTerm::MemoryLoad(point, address, _) =
            crate::kernel::equality_graph::logical_pointer_read_term(value.address())?
        else {
            return None;
        };
        Some(Self::shared_pointer_read(
            SharedPointer::import(value),
            point.into(),
            SharedAddress::import(address.address()),
        ))
    }

    pub(crate) fn shared_pointer_read(
        value: SharedPointer,
        point: ProgramPoint,
        address: SharedAddress,
    ) -> Self {
        Self::intern(
            KernelType::Program(value.node().program_type),
            KernelTermNode::PointerRead {
                value,
                point,
                address,
            },
        )
    }

    /// Selected native read leaf for consumers still using the native atom
    /// interface. Never expands a surrounding shared arithmetic expression.
    pub(crate) fn machine_read_leaf(&self) -> Option<&MachineTerm> {
        let KernelTermNode::MemoryLoad {
            point,
            address,
            kind,
        } = self.node()
        else {
            return None;
        };
        Some(self.0.machine_leaf.get_or_init(|| {
            crate::kernel::MachineTerm::read_named(
                point.clone(),
                address.export().expect("retained read address"),
                *kind,
            )
        }))
    }

    #[cfg(test)]
    pub(crate) fn has_cached_machine_leaf(&self) -> bool {
        self.0.machine_leaf.0.get().is_some()
    }

    pub(crate) fn scalar_read_descriptor(
        format: MachineIntegerType,
        point: &ProgramPoint,
        address: &Address,
        kind: LoadKind,
    ) -> Option<Self> {
        let address = Self::scalar_read_address(address)?;
        Some(Self::shared_scalar_read_descriptor(
            format, point, &address, kind,
        ))
    }

    /// Prepare the immutable address at a native read's admission boundary.
    pub(crate) fn scalar_read_address(address: &Address) -> Option<SharedAddress> {
        if !exact_address(address) {
            return None;
        }
        Some(SharedAddress::import(address))
    }

    /// Retain the selected common address. This only constructs read syntax;
    /// memory selection, access evidence and value resolution stay with callers.
    pub(crate) fn shared_scalar_read_descriptor(
        format: MachineIntegerType,
        point: &ProgramPoint,
        address: &SharedAddress,
        kind: LoadKind,
    ) -> Self {
        Self::intern(
            KernelType::Program(format.program_type()),
            KernelTermNode::MemoryLoad {
                point: point.clone(),
                address: address.clone(),
                kind,
            },
        )
    }
}

/// Native pointer equality can omit auxiliary metadata in opaque machine
/// payloads. Do not use it to intern such a payload: those addresses retain
/// the producer-local legacy boundary until their own shared forms migrate.
/// Shared index identities include their nested read states, so admitting
/// an address never re-walks the retained index expression.
fn exact_address(address: &Address) -> bool {
    let mut pending = vec![&address.offset];
    while let Some(offset) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match offset {
            AddressOffset::Constant(_) | AddressOffset::Variable(_) => {}
            AddressOffset::Add(a, b) => pending.extend([b.as_ref(), a.as_ref()]),
            AddressOffset::Int32Scaled { value, .. } | AddressOffset::Int64Scaled { value, .. } => {
                // The child identity already includes every read state.
                // Never export or walk its retained expression prefix here.
                if value.shared_operand().is_none() {
                    return false;
                }
            }
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::VerificationSession;

    #[test]
    fn pointer_read_execution_results_keep_definition_type_and_complete_payload() {
        let _session = VerificationSession::enter();
        let memory = SymbolicMemory::new();
        let address = Address::symbolic(Variable(1018000));
        for ty in [
            ProgramType::Int32Pointer,
            ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED),
        ] {
            let ProgramValue::Pointer(pointer) = memory.symbolic_pointer_load(None, &address, ty)
            else {
                panic!("pointer producer");
            };
            let pointer = pointer;
            let expected = SharedPointer::import(&pointer);
            let native = ProgramValue::Pointer(pointer);
            let result = crate::kernel::ExecutionValue::retain_native(native.clone());
            let root = result.shared().expect("retained pointer read");
            let KernelTermNode::PointerRead {
                value,
                point: retained_point,
                address: cell,
            } = root.node()
            else {
                panic!("pointer read root");
            };
            let retained_state = retained_point.shared_memory();
            assert_eq!(root.ty(), &KernelType::Program(ty));
            assert_eq!(
                retained_state.arena_id(),
                intern_memory(memory.clone()).arena_id()
            );
            assert_eq!(cell, &SharedAddress::import(&address));
            assert!(value.same_source_payload(&expected));
            assert!(root.0.argument_leaf.get().is_none());
            let ProgramValue::Pointer(restored) = result.native_payload().unwrap() else {
                panic!("compatibility value");
            };
            assert!(SharedPointer::import(restored).same_source_payload(&expected));
            assert_eq!(result.clone().into_native(), native);
            // Locals retain their existing compatibility policy until their slice.
            assert_eq!(
                crate::kernel::StoredExecutionValue::from(result).into_native(),
                native
            );
        }
    }

    #[test]
    fn pointer_read_root_retains_definition_after_registry_reset() {
        let _session = VerificationSession::enter();
        let address = Address::symbolic(Variable(1018001));
        let memory = SymbolicMemory::new();
        let native = memory.symbolic_pointer_load(None, &address, ProgramType::UInt8Pointer);
        let retained = crate::kernel::ExecutionValue::retain_native(native);
        let root = retained.shared().expect("read root").clone();
        crate::kernel::eval::clear_load_variable_registry();
        crate::kernel::equality_graph::clear_logical_pointer_reads();
        let KernelTermNode::PointerRead {
            point: retained_point,
            address: cell,
            ..
        } = root.node()
        else {
            panic!("read root");
        };
        let retained_state = retained_point.shared_memory();
        assert_eq!(retained_state.arena_id(), intern_memory(memory).arena_id());
        assert_eq!(cell, &SharedAddress::import(&address));
        assert!(matches!(
            root.old_pointer_value(),
            Some(ProgramValue::Pointer(_))
        ));
    }

    #[test]
    fn scalar_reads_retain_exact_descriptors_and_survive_registry_reset() {
        let _session = VerificationSession::enter();
        let address = Address::symbolic(Variable(993100));
        let memory = intern_memory(SymbolicMemory::new().store(
            address.clone(),
            ProgramValue::Int32(MachineTerm::constant(7)),
        ));
        for (kind, format) in [
            (LoadKind::Int8, MachineIntegerType::Int8),
            (LoadKind::UInt8, MachineIntegerType::UInt8),
            (LoadKind::Int16, MachineIntegerType::Int16),
            (LoadKind::UInt16, MachineIntegerType::UInt16),
            (LoadKind::Int32, MachineIntegerType::Int32),
            (LoadKind::UInt32, MachineIntegerType::UInt32),
            (LoadKind::Bits64, MachineIntegerType::UInt64),
            (LoadKind::Int128, MachineIntegerType::Int128),
            (LoadKind::UInt128, MachineIntegerType::UInt128),
        ] {
            let native = crate::kernel::MachineTerm::read_named(
                ProgramPoint::at(&memory),
                address.clone(),
                kind,
            );
            let term = KernelTermImport::default().machine(format, &native);
            assert!(
                matches!(term.node(), KernelTermNode::MemoryLoad { point: m, address: p, kind: k } if m.shared_memory() == &memory && p == &SharedAddress::import(&address) && *k == kind)
            );
            assert!(term.is_shared_machine_operand());
            crate::kernel::eval::clear_load_variable_registry();
            assert_eq!(
                crate::kernel::MachineOperandView::Shared(&term)
                    .read_source()
                    .as_deref(),
                Some(&native)
            );
            assert_eq!(KernelTermExport::machine(&term).unwrap(), native);
            assert_eq!(KernelTermImport::default().machine(format, &native), term);
        }
    }

    #[test]
    fn shared_read_addresses_preserve_call_payloads_ignored_by_logical_identity() {
        let _session = VerificationSession::enter();
        let memory = intern_memory(SymbolicMemory::new());
        let pointer = OldPointer::new(
            Address::symbolic(Variable(1017200)),
            ProgramType::Int32Pointer,
        );
        let mut outputs = Vec::new();
        let mut roots = Vec::new();
        for constant in [false, true] {
            let call = SharedPureApplication::intern(
                "read_address".into(),
                vec![PureFunctionArgument::Value(ProgramValue::Pointer(
                    pointer
                        .clone()
                        .with_declared_object_class(constant.then_some(
                            crate::kernel::effective_type::CAccessClass::Scalar(
                                crate::kernel::effective_type::CScalarClass::Int,
                            ),
                        )),
                ))],
            );
            let payload = call.payload_id();
            let address = Address {
                base: AddressBase::PureFunctionApplication(call),
                offset: AddressOffset::Constant(0),
            };
            let root = KernelTerm::scalar_read_descriptor(
                MachineIntegerType::Int32,
                &crate::kernel::ProgramPoint::at(&memory),
                &address,
                LoadKind::Int32,
            )
            .unwrap();
            let output = KernelTermExport::machine(&root).unwrap();
            let MachineTerm::MemoryLoad(_, address, _) = &output else {
                panic!("read")
            };
            let AddressBase::PureFunctionApplication(call) = &address.base else {
                panic!("call address")
            };
            assert_eq!(call.payload_id(), payload);
            let [PureFunctionArgument::Value(ProgramValue::Pointer(argument))] = call.arguments()
            else {
                panic!("pointer argument")
            };
            assert_eq!(argument.object_class().is_some(), constant);
            roots.push(root);
            outputs.push(output);
        }
        assert_eq!(
            outputs[0], outputs[1],
            "native logical read identity is unchanged"
        );
        assert_ne!(roots[0], roots[1], "exact payloads must not coalesce");
    }

    #[test]
    fn scalar_read_identity_distinguishes_state_address_and_kind() {
        let _session = VerificationSession::enter();
        let address = Address::symbolic(Variable(993110));
        let memory = intern_memory(SymbolicMemory::new());
        let written = intern_memory(SymbolicMemory::new().store(
            address.clone(),
            ProgramValue::Int32(MachineTerm::constant(7)),
        ));
        let load = |memory, address, kind| {
            KernelTermImport::default().machine(
                MachineIntegerType::Int32,
                &crate::kernel::MachineTerm::read_named(memory, address, kind),
            )
        };
        let first = load(ProgramPoint::at(&memory), address.clone(), LoadKind::Int32);
        assert_ne!(
            first,
            load(ProgramPoint::at(&written), address.clone(), LoadKind::Int32)
        );
        assert_ne!(
            first,
            load(
                ProgramPoint::at(&memory),
                Address::symbolic(Variable(993111)),
                LoadKind::Int32
            )
        );
        assert_ne!(
            first,
            load(ProgramPoint::at(&memory), address, LoadKind::UInt32)
        );
    }

    #[test]
    fn registered_read_handle_imports_as_its_owned_read_descriptor() {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let raw = crate::kernel::MachineTerm::read_named(
            ProgramPoint::at(&(intern_memory(SymbolicMemory::new()))),
            Address::symbolic(Variable(993120)),
            LoadKind::Int32,
        );
        let (name, descriptor) = crate::kernel::eval::load_variable_for_term(&raw).unwrap();
        let term = crate::kernel::eval::registered_scalar_read_term(&name, format).unwrap();
        assert!(matches!(term.node(), KernelTermNode::MemoryLoad { .. }));
        assert_eq!(
            term,
            KernelTermImport::default().machine(format, &descriptor)
        );
        crate::kernel::eval::clear_load_variable_registry();
        assert_eq!(KernelTermExport::machine(&term).unwrap(), descriptor);
    }
    #[test]
    fn named_read_import_and_arithmetic_storage_retain_the_same_descriptor() {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::UInt32;
        let raw = crate::kernel::MachineTerm::read_named(
            ProgramPoint::at(&(intern_memory(SymbolicMemory::new()))),
            Address::symbolic(Variable(993126)),
            LoadKind::UInt32,
        );
        let (name, descriptor) = crate::kernel::eval::load_variable_for_term(&raw).unwrap();
        let named = MachineTerm::Variable(name);
        let arithmetic = KernelTermImport::default()
            .machine_arithmetic(format, &named)
            .unwrap();
        let general = KernelTermImport::default().machine(format, &named);
        assert_eq!(general, arithmetic);
        assert_eq!(KernelTermExport::machine(&general).unwrap(), descriptor);
        crate::kernel::eval::clear_load_variable_registry();
        assert_eq!(
            KernelTermImport::default().machine(format, &descriptor),
            general
        );
        assert_eq!(KernelTermExport::machine(&arithmetic).unwrap(), descriptor);
    }

    #[test]
    fn registered_read_cache_follows_registry_capture_and_restore() {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let raw = crate::kernel::MachineTerm::read_named(
            ProgramPoint::at(&(intern_memory(SymbolicMemory::new()))),
            Address::symbolic(Variable(993125)),
            LoadKind::Int32,
        );
        let (name, descriptor) = crate::kernel::eval::load_variable_for_term(&raw).unwrap();
        let term = crate::kernel::eval::registered_scalar_read_term(&name, format).unwrap();
        let registry = crate::kernel::eval::capture_load_variable_registry();
        crate::kernel::eval::clear_load_variable_registry();
        assert!(crate::kernel::eval::registered_scalar_read_term(&name, format).is_none());
        crate::kernel::eval::restore_load_variable_registry(&registry);
        assert_eq!(
            crate::kernel::eval::registered_scalar_read_term(&name, format).unwrap(),
            term
        );
        assert_eq!(KernelTermExport::machine(&term).unwrap(), descriptor);
    }

    #[test]
    fn nested_scalar_reads_retain_both_states_without_registered_names() {
        let _session = VerificationSession::enter();
        let p = Address::symbolic(Variable(993140));
        let before = intern_memory(SymbolicMemory::new());
        let after = intern_memory(
            SymbolicMemory::new().store(p.clone(), ProgramValue::Int32(MachineTerm::constant(1))),
        );
        let nested = |inner: SharedMemory, outer: SharedMemory, kind| {
            crate::kernel::MachineTerm::read_named(
                ProgramPoint::at(&outer),
                Address {
                    base: AddressBase::Symbolic(Variable(993141)),
                    offset: AddressOffset::scaled_int32_node(
                        MachineTerm::read_named(
                            ProgramPoint::at(&inner),
                            Box::new(p.clone()),
                            kind,
                        ),
                        4,
                    ),
                },
                LoadKind::Int32,
            )
        };
        let raw = nested(before.clone(), after.clone(), LoadKind::Int32);
        let term = KernelTermImport::default().machine(MachineIntegerType::Int32, &raw);
        assert!(matches!(term.node(), KernelTermNode::MemoryLoad { .. }));
        for other in [
            nested(after.clone(), after.clone(), LoadKind::Int32),
            nested(before.clone(), before.clone(), LoadKind::Int32),
            nested(before, after, LoadKind::UInt32),
        ] {
            assert_ne!(
                term,
                KernelTermImport::default().machine(MachineIntegerType::Int32, &other)
            );
        }
        crate::kernel::eval::clear_load_variable_registry();
        assert_eq!(KernelTermExport::machine(&term).unwrap(), raw);
        assert_eq!(
            term,
            KernelTermImport::default().machine(MachineIntegerType::Int32, &raw)
        );
    }

    #[test]
    fn nested_read_identity_does_not_compare_state_contents_across_arenas() {
        let first = {
            let _session = VerificationSession::enter();
            intern_memory(SymbolicMemory::new())
        };
        let _session = VerificationSession::enter();
        // Reads of the first session's memory, on purpose.
        let _cross_arena = crate::kernel::primitives::allow_cross_arena_loads();
        let second = intern_memory(SymbolicMemory::new());
        assert_ne!(first.arena_id(), second.arena_id());
        assert_eq!(first, second); // Same contents, distinct retained_state identities.
        let read = |memory| {
            crate::kernel::MachineTerm::read_named(
                memory,
                Address::symbolic(Variable(993150)),
                LoadKind::Int32,
            )
        };
        let offset = AddressOffset::scaled_int32_node(read(ProgramPoint::at(&first)), 4);
        assert_eq!(offset.map_scaled_operands(Clone::clone), offset);
        assert_ne!(
            offset.map_scaled_operands(|value| SharedMachineIntegerTerm::index(
                value.ty(),
                read(ProgramPoint::at(&second))
            )),
            offset
        );
        let outer = second.clone();
        let import = |inner| {
            KernelTermImport::default().machine(
                MachineIntegerType::Int32,
                &crate::kernel::MachineTerm::read_named(
                    ProgramPoint::at(&outer),
                    Address {
                        base: AddressBase::Symbolic(Variable(993151)),
                        offset: AddressOffset::scaled_int32_node(
                            MachineTerm::read_named(
                                inner,
                                Box::new(Address::symbolic(Variable(993150))),
                                LoadKind::Int32,
                            ),
                            4,
                        ),
                    },
                    LoadKind::Int32,
                ),
            )
        };
        let first_term = import(ProgramPoint::at(&first));
        let second_term = import(ProgramPoint::at(&second));
        assert!(matches!(
            first_term.node(),
            KernelTermNode::MemoryLoad { .. }
        ));
        assert_ne!(first_term, second_term);
        assert_eq!(first_term, import(ProgramPoint::at(&first)));
    }

    #[test]
    fn index_producers_retain_structural_reads_despite_a_cached_written_name() {
        let _session = VerificationSession::enter();
        for (format, kind, wide) in [
            (MachineIntegerType::Int32, LoadKind::Int32, false),
            (MachineIntegerType::Int64, LoadKind::Bits64, true),
        ] {
            let read = crate::kernel::MachineTerm::read_named(
                ProgramPoint::at(&(intern_memory(SymbolicMemory::new()))),
                Address::symbolic(Variable(993160)),
                kind,
            );
            let (name, descriptor) = crate::kernel::eval::load_variable_for_term(&read).unwrap();
            let written = SharedMachineIntegerTerm::intern(format, MachineTerm::Variable(name));
            assert!(matches!(written.value(), MachineTerm::Variable(_)));
            let mut facts = crate::kernel::ExecutionFacts::new();
            let index = crate::kernel::canonicalized_offset_index_term(
                MachineTerm::Variable(name),
                &mut facts,
            );
            assert_eq!(index, descriptor);
            let offset = if wide {
                AddressOffset::scaled_int64_node(index, 4, true)
            } else {
                AddressOffset::scaled_int32_node(index, 4)
            };
            let (AddressOffset::Int32Scaled { value, .. }
            | AddressOffset::Int64Scaled { value, .. }) = &offset
            else {
                unreachable!()
            };
            assert!(matches!(
                value.shared_operand().unwrap().node(),
                KernelTermNode::MemoryLoad { .. }
            ));
            crate::kernel::eval::clear_load_variable_registry();
            assert_eq!(value.structural_value(), &descriptor);
            let restored = if wide {
                AddressOffset::scaled_int64_node(value.structural_value().clone(), 4, true)
            } else {
                AddressOffset::scaled_int32_node(value.structural_value().clone(), 4)
            };
            assert_eq!(offset, restored);
        }
    }

    #[test]
    fn forming_an_outer_read_does_not_fold_the_index_read_to_its_stored_value() {
        let _session = VerificationSession::enter();
        let p = Address::symbolic(Variable(993162));
        let memory = intern_memory(
            SymbolicMemory::new().store(p.clone(), ProgramValue::Int32(MachineTerm::constant(3))),
        );
        let index = crate::kernel::eval::canonical_form_of_load(memory.clone(), p, LoadKind::Int32);
        let address = Address {
            base: AddressBase::Symbolic(Variable(993163)),
            offset: AddressOffset::scaled_int32_node(index, 4),
        };
        let outer =
            crate::kernel::eval::canonical_form_of_load(memory, address.clone(), LoadKind::Int32);
        let shared = KernelTermImport::default().machine(MachineIntegerType::Int32, &outer);
        let KernelTermNode::MemoryLoad {
            address: actual, ..
        } = shared.node()
        else {
            panic!("outer read")
        };
        assert_eq!(actual, &SharedAddress::import(&address));
        let KernelAddressOffset::Int32Scaled { value, .. } = actual.node().offset.node() else {
            panic!("index read retained")
        };
        assert!(matches!(value.node(), KernelTermNode::MemoryLoad { .. }));
    }

    #[test]
    fn opaque_index_identity_does_not_replace_its_annotation_payload() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        let _session = VerificationSession::enter();
        let mut retained = Vec::new();
        for class in [CScalarClass::Int, CScalarClass::Char] {
            let expected = Some(CAccessClass::Scalar(class));
            let index = AddressOffset::scaled_int64_node(
                MachineTerm::IntegerAddress(
                    Box::new(Address::symbolic(Variable(993161))),
                    crate::kernel::AddressObjectClass::new(expected.clone()),
                ),
                1,
                true,
            );
            let AddressOffset::Int64Scaled { value, .. } = &index else {
                unreachable!()
            };
            assert!(value.shared_operand().is_none());
            let MachineTerm::IntegerAddress(_, actual) = value.structural_value() else {
                panic!("address payload")
            };
            assert_eq!(actual.class(), expected);
            retained.push(index);
        }
        assert_eq!(retained[0], retained[1]); // The annotations are not numeric identity.
    }

    #[test]
    fn read_addresses_outside_the_shared_fragment_keep_the_exact_legacy_payload() {
        let _session = VerificationSession::enter();
        let address = Address {
            base: AddressBase::Symbolic(Variable(993130)),
            offset: AddressOffset::scaled_int32_node(
                MachineTerm::IntegerAddress(
                    Box::new(Address::symbolic(Variable(993131))),
                    crate::kernel::AddressObjectClass::NONE,
                ),
                4,
            ),
        };
        let native = crate::kernel::MachineTerm::read_named(
            ProgramPoint::at(&(intern_memory(SymbolicMemory::new()))),
            address,
            LoadKind::Int32,
        );
        let term = KernelTermImport::default().machine(MachineIntegerType::Int32, &native);
        assert!(matches!(term.node(), KernelTermNode::ImportedScalar(_)));
        assert_eq!(KernelTermExport::machine(&term).unwrap(), native);
    }
}
