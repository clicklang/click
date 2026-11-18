//! Prepared readers for shared pointer components. Each mode retains the
//! native distinction between syntax, connections, capture and bound variables.
use super::retained_folds::{FoldVariableRead, collect_argument, common_variables};
use super::*;
use crate::kernel::{KernelAddressOffset, SharedAddress, SharedAddressOffset, SharedPointer};

enum Component<'a> {
    Block(&'a AddressBase),
    Coordinate(Variable),
    Index(&'a KernelTerm),
}

fn visit_components<'a>(
    addresses: impl IntoIterator<Item = &'a SharedAddress>,
    mut visit: impl FnMut(Component<'a>),
) {
    let mut seen = std::collections::HashSet::<&SharedAddressOffset>::new();
    for address in addresses {
        if checked_collection_checkpoint() {
            return;
        }
        visit(Component::Block(address.node().base.native_atom()));
        let mut pending = vec![&address.node().offset];
        while let Some(offset) = pending.pop() {
            if checked_collection_checkpoint() {
                return;
            }
            if !seen.insert(offset) {
                continue;
            }
            match offset.node() {
                KernelAddressOffset::Constant(_) => {}
                KernelAddressOffset::Variable(variable) => visit(Component::Coordinate(*variable)),
                KernelAddressOffset::Add([left, right]) => pending.extend([right, left]),
                KernelAddressOffset::Int32Scaled { value, .. }
                | KernelAddressOffset::Int64Scaled { value, .. } => visit(Component::Index(value)),
            }
        }
    }
}

pub(super) fn collect_offset_variables_with_summaries(
    offsets: &[SharedAddressOffset; 2],
    mode: FoldVariableRead,
    variables: &mut BTreeSet<Variable>,
    summaries: &mut std::collections::HashMap<u64, crate::persistent::PersistentSet<Variable>>,
) {
    SharedAddressOffset::visit_pair(offsets, |node| {
        if checked_collection_checkpoint() {
            return;
        }
        match node {
            KernelAddressOffset::Variable(variable)
                if mode == FoldVariableRead::ExpressionFree
                    && (collecting_connection_variables()
                        || COORDINATE_VARIABLES.with(std::cell::Cell::get)) =>
            {
                variables.insert(*variable);
            }
            node => {
                if let Some(root) = node.index() {
                    variables.extend(common_variables(root, mode, summaries).iter().copied());
                }
            }
        }
    });
}

pub(crate) fn collect_address_variables(
    address: &SharedAddress,
    mode: FoldVariableRead,
    variables: &mut BTreeSet<Variable>,
) {
    collect_addresses(std::iter::once(address), mode, variables);
}

pub(crate) fn collect_pointer_variables(
    pointer: &SharedPointer,
    mode: FoldVariableRead,
    variables: &mut BTreeSet<Variable>,
) {
    // The native ProgramValue Integer-free reader treats pointers as opaque.
    // Its expression/capture/binder readers visit address roles, not bounds widths.
    if mode != FoldVariableRead::IntegerFree {
        collect_addresses(pointer.addresses(), mode, variables);
    }
}

fn collect_addresses<'a>(
    addresses: impl IntoIterator<Item = &'a SharedAddress>,
    mode: FoldVariableRead,
    variables: &mut BTreeSet<Variable>,
) {
    collect_addresses_with_summaries(addresses, mode, variables, &mut Default::default());
}

/// A read address is a child of the enclosing common term traversal. Share its
/// memo so diamonds of nested reads do not revisit their common prefixes.
pub(super) fn collect_address_variables_with_summaries(
    address: &SharedAddress,
    mode: FoldVariableRead,
    variables: &mut BTreeSet<Variable>,
    summaries: &mut std::collections::HashMap<u64, crate::persistent::PersistentSet<Variable>>,
) {
    collect_addresses_with_summaries(std::iter::once(address), mode, variables, summaries);
}

fn collect_addresses_with_summaries<'a>(
    addresses: impl IntoIterator<Item = &'a SharedAddress>,
    mode: FoldVariableRead,
    variables: &mut BTreeSet<Variable>,
    summaries: &mut std::collections::HashMap<u64, crate::persistent::PersistentSet<Variable>>,
) {
    let mut native_seen = SeenTerms::default();
    visit_components(addresses, |component| match component {
        Component::Block(block) if mode == FoldVariableRead::ExpressionFree => {
            collect_address_base_bitvector_variables(block, variables);
        }
        Component::Block(AddressBase::PureFunctionApplication(application)) => {
            if native_seen.pointers.insert(application.id()) {
                for argument in application.arguments() {
                    collect_argument(argument, mode, variables, &mut native_seen);
                }
            }
        }
        Component::Block(
            AddressBase::Symbolic(variable)
            | AddressBase::FunctionSymbolic(variable)
            | AddressBase::ExternalObject(variable),
        ) if mode == FoldVariableRead::MachineCapture => {
            variables.insert(*variable);
        }
        Component::Coordinate(variable)
            if mode == FoldVariableRead::ExpressionFree
                && (collecting_connection_variables()
                    || COORDINATE_VARIABLES.with(std::cell::Cell::get)) =>
        {
            variables.insert(variable);
        }
        Component::Index(root) => {
            variables.extend(common_variables(root, mode, summaries).iter().copied());
        }
        _ => {}
    });
}

pub(crate) fn address_scope_summary(
    address: &SharedAddress,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    addresses_scope_summary(std::iter::once(address), summaries)
}
pub(crate) fn pointer_scope_summary(
    pointer: &SharedPointer,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    addresses_scope_summary(pointer.addresses(), summaries)
}
fn addresses_scope_summary<'a>(
    addresses: impl IntoIterator<Item = &'a SharedAddress>,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    let mut result = IntegerScopeSummary::default();
    visit_components(addresses, |component| match component {
        Component::Block(
            AddressBase::Symbolic(variable)
            | AddressBase::FunctionSymbolic(variable)
            | AddressBase::ExternalObject(variable),
        ) => result.reserve(*variable),
        Component::Index(root) => result.merge(collect_machine_operand_scope_summary(
            MachineOperandView::Shared(root),
            summaries,
        )),
        _ => {}
    });
    result
}

pub(super) fn collect_pointer_bound_identities(
    pointer: &SharedPointer,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
) {
    // This distinct native query visits only opaque pointer-call arguments.
    for address in pointer.addresses() {
        if checked_collection_checkpoint() {
            return;
        }
        if let AddressBase::PureFunctionApplication(application) = address.node().base.native_atom()
            && seen.pointers.insert(application.id())
        {
            for argument in application.arguments() {
                collect_pure_argument_bound_identities(argument, variables, seen);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    pub(super) fn native_variables(
        pointer: &Address,
        mode: FoldVariableRead,
    ) -> BTreeSet<Variable> {
        let mut result = BTreeSet::new();
        let mut seen = SeenTerms::default();
        match mode {
            FoldVariableRead::IntegerFree => {
                collect_pointer_integer_variables(pointer, &mut result, &mut seen)
            }
            FoldVariableRead::ExpressionFree => {
                collect_pointer_bitvector_variables(pointer, &mut result)
            }
            FoldVariableRead::MachineCapture => {
                collect_pointer_capture_variables(pointer, &mut result, &mut seen)
            }
            FoldVariableRead::IntegerBinders | FoldVariableRead::MachineBinders => {
                let mut integers = BTreeSet::new();
                let mut machines = BTreeSet::new();
                collect_pointer_binder_variables(pointer, &mut integers, &mut machines, &mut seen);
                result = if mode == FoldVariableRead::IntegerBinders {
                    integers
                } else {
                    machines
                };
            }
        }
        result
    }
    const MODES: [FoldVariableRead; 5] = [
        FoldVariableRead::IntegerFree,
        FoldVariableRead::ExpressionFree,
        FoldVariableRead::MachineCapture,
        FoldVariableRead::IntegerBinders,
        FoldVariableRead::MachineBinders,
    ];
    #[test]
    fn shared_address_readers_match_native_modes_without_export() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = intern_memory(SymbolicMemory::new());
        let cases = [
            Address {
                base: AddressBase::Symbolic(Variable(1001001)),
                offset: AddressOffset::scaled_int64_node(
                    MachineTerm::Variable(Variable(1001002)),
                    8,
                    true,
                ),
            },
            Address {
                base: AddressBase::PureFunctionApplication(SharedPureApplication::intern(
                    "dependency_call".into(),
                    vec![PureFunctionArgument::Integer(
                        IntegerTerm::Variable(Variable(1001003)).into(),
                    )],
                )),
                offset: AddressOffset::Variable(Variable(1001004)),
            },
            Address::loaded_value(&memory, &Address::symbolic(Variable(1001005))),
        ];
        for source in cases {
            let shared = SharedAddress::import(&source);
            for mode in MODES {
                let expected = native_variables(&source, mode);
                let exports = KernelTermExport::machine_export_count();
                let mut actual = BTreeSet::new();
                collect_address_variables(&shared, mode, &mut actual);
                assert_eq!(actual, expected, "{mode:?}: {source:?}");
                assert_eq!(KernelTermExport::machine_export_count(), exports);
            }
            assert_eq!(
                address_scope_summary(&shared, &mut Default::default()).max,
                collect_pointer_scope_summary(&source, &mut Default::default()).max
            );
        }
    }
    #[test]
    fn pointer_indices_and_calls_keep_fold_capture_and_binder_rules() {
        let _session = crate::kernel::VerificationSession::enter();
        let fold: SharedIntegerTerm = IntegerTerm::RangeFold {
            index: IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::Variable(Variable(1001020)).into(),
            },
            initial: IntegerTerm::constant_i64(0).into(),
            accumulator: Variable(1001021),
            item: Variable(1001022),
            body: IntegerTerm::Variable(Variable(1001022)).into(),
        }
        .into();
        let address = Address {
            base: AddressBase::PureFunctionApplication(SharedPureApplication::intern(
                "fold_pointer".into(),
                vec![PureFunctionArgument::Integer(fold.clone())],
            )),
            offset: AddressOffset::scaled_int32_node(
                MachineTerm::IntegerToMachine {
                    value: fold,
                    destination: MachineIntegerType::Int32,
                },
                4,
            ),
        };
        let shared = SharedAddress::import(&address);
        for mode in MODES {
            let mut actual = BTreeSet::new();
            collect_address_variables(&shared, mode, &mut actual);
            assert_eq!(actual, native_variables(&address, mode), "{mode:?}");
        }
        let source = Pointer::new(address, ProgramType::VoidPointer);
        let shared = SharedPointer::import(&source);
        let mut expected = BTreeSet::new();
        collect_program_value_bound_identities(
            &ProgramValue::Pointer(source),
            &mut expected,
            &mut SeenTerms::default(),
        );
        let mut actual = BTreeSet::new();
        collect_pointer_bound_identities(&shared, &mut actual, &mut SeenTerms::default());
        assert_eq!(actual, expected);
        assert!(actual.contains(&Variable(1001021)));
        assert!(actual.contains(&Variable(1001022)));
    }
    #[test]
    fn complete_pointer_readers_keep_native_metadata_and_coordinate_policy() {
        let _session = crate::kernel::VerificationSession::enter();
        let source = Pointer::new(
            Address::symbolic(Variable(1001010)),
            ProgramType::VoidPointer,
        )
        .with_provenance(Arc::new(Address::symbolic(Variable(1001011))))
        .with_bounds_owner(Some(Arc::new(Address::symbolic(Variable(1001012)))))
        .with_bounds(Some(SubobjectBounds {
            start: Address::symbolic(Variable(1001013)),
            width: MachineTerm::Variable(Variable(1001014)),
        }));
        let shared = SharedPointer::import(&source);
        for mode in MODES {
            let mut actual = BTreeSet::new();
            collect_pointer_variables(&shared, mode, &mut actual);
            let expected = if mode == FoldVariableRead::IntegerFree {
                BTreeSet::new()
            } else {
                source
                    .pointers()
                    .flat_map(|address| native_variables(address, mode))
                    .collect()
            };
            assert_eq!(actual, expected, "{mode:?}");
        }
        assert_eq!(
            pointer_scope_summary(&shared, &mut Default::default()).max,
            collect_program_value_scope_summary(
                &ProgramValue::Pointer(source),
                &mut Default::default()
            )
            .max
        );
        let source = Address {
            base: AddressBase::ExternalArgument,
            offset: AddressOffset::Variable(Variable(1001015)),
        };
        let shared = SharedAddress::import(&source);
        let before = COORDINATE_VARIABLES.with(|flag| flag.replace(true));
        let expected = native_variables(&source, FoldVariableRead::ExpressionFree);
        let mut actual = BTreeSet::new();
        collect_address_variables(&shared, FoldVariableRead::ExpressionFree, &mut actual);
        COORDINATE_VARIABLES.with(|flag| flag.set(before));
        assert_eq!(actual, expected);
        assert!(actual.contains(&Variable(1001015)));
    }
}
#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/reasoning/variable_collection/retained_pointers.rs");
}
