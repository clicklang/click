//! Prepared readers for shared pointer components. Each mode retains the
//! native distinction between syntax, connections, capture and bound variables.
use super::retained_folds::{FoldVariableRead, collect_argument, common_variables};
use super::*;
use crate::kernel::{
    KernelPointerOffset, SharedPointerAddress, SharedPointerOffset, SharedPointerValue,
};

enum Component<'a> {
    Block(&'a PointerBlock),
    Coordinate(Variable),
    Index(&'a KernelTerm),
}

fn visit_components<'a>(
    addresses: impl IntoIterator<Item = &'a SharedPointerAddress>,
    mut visit: impl FnMut(Component<'a>),
) {
    let mut seen = std::collections::HashSet::<&SharedPointerOffset>::new();
    for address in addresses {
        if checked_collection_checkpoint() {
            return;
        }
        visit(Component::Block(address.node().block.native_atom()));
        let mut pending = vec![&address.node().offset];
        while let Some(offset) = pending.pop() {
            if checked_collection_checkpoint() {
                return;
            }
            if !seen.insert(offset) {
                continue;
            }
            match offset.node() {
                KernelPointerOffset::Constant(_) => {}
                KernelPointerOffset::Variable(variable) => visit(Component::Coordinate(*variable)),
                KernelPointerOffset::Add([left, right]) => pending.extend([right, left]),
                KernelPointerOffset::Int32Scaled { value, .. }
                | KernelPointerOffset::Int64Scaled { value, .. } => visit(Component::Index(value)),
            }
        }
    }
}

pub(crate) fn collect_address_variables(
    address: &SharedPointerAddress,
    mode: FoldVariableRead,
    variables: &mut BTreeSet<Variable>,
) {
    collect_addresses(std::iter::once(address), mode, variables);
}

pub(crate) fn collect_pointer_variables(
    pointer: &SharedPointerValue,
    mode: FoldVariableRead,
    variables: &mut BTreeSet<Variable>,
) {
    // The native ProgramValue Integer-free reader treats pointers as opaque.
    // Its expression/capture/binder readers visit address roles, not extent widths.
    if mode != FoldVariableRead::IntegerFree {
        collect_addresses(pointer.addresses(), mode, variables);
    }
}

fn collect_addresses<'a>(
    addresses: impl IntoIterator<Item = &'a SharedPointerAddress>,
    mode: FoldVariableRead,
    variables: &mut BTreeSet<Variable>,
) {
    let mut summaries = std::collections::HashMap::new();
    let mut native_seen = SeenTerms::default();
    visit_components(addresses, |component| match component {
        Component::Block(block) if mode == FoldVariableRead::ExpressionFree => {
            collect_pointer_block_bitvector_variables(block, variables);
        }
        Component::Block(PointerBlock::PureFunctionApplication(application)) => {
            if native_seen.pointers.insert(application.id()) {
                for argument in application.arguments() {
                    collect_argument(argument, mode, variables, &mut native_seen);
                }
            }
        }
        Component::Block(
            PointerBlock::Symbolic(variable)
            | PointerBlock::FunctionSymbolic(variable)
            | PointerBlock::ExternalObject(variable),
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
            variables.extend(common_variables(root, mode, &mut summaries).iter().copied());
        }
        _ => {}
    });
}

pub(crate) fn address_scope_summary(
    address: &SharedPointerAddress,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    addresses_scope_summary(std::iter::once(address), summaries)
}
pub(crate) fn pointer_scope_summary(
    pointer: &SharedPointerValue,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    addresses_scope_summary(pointer.addresses(), summaries)
}
fn addresses_scope_summary<'a>(
    addresses: impl IntoIterator<Item = &'a SharedPointerAddress>,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    let mut result = IntegerScopeSummary::default();
    visit_components(addresses, |component| match component {
        Component::Block(
            PointerBlock::Symbolic(variable)
            | PointerBlock::FunctionSymbolic(variable)
            | PointerBlock::ExternalObject(variable),
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
    pointer: &SharedPointerValue,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
) {
    // This distinct native query visits only opaque pointer-call arguments.
    for address in pointer.addresses() {
        if checked_collection_checkpoint() {
            return;
        }
        if let PointerBlock::PureFunctionApplication(application) =
            address.node().block.native_atom()
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
        pointer: &Pointer,
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
        let memory = intern_memory(Memory::new());
        let cases = [
            Pointer {
                block: PointerBlock::Symbolic(Variable(1001001)),
                offset: PointerOffsetTerm::scaled_int64_node(
                    MachineTerm::Variable(Variable(1001002)),
                    8,
                    true,
                ),
            },
            Pointer {
                block: PointerBlock::PureFunctionApplication(SharedPureApplication::intern(
                    "dependency_call".into(),
                    vec![PureFunctionArgument::Integer(
                        IntegerTerm::Variable(Variable(1001003)).into(),
                    )],
                )),
                offset: PointerOffsetTerm::Variable(Variable(1001004)),
            },
            Pointer::loaded_value(&memory, &Pointer::symbolic(Variable(1001005))),
        ];
        for source in cases {
            let shared = SharedPointerAddress::import(&source);
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
        let address = Pointer {
            block: PointerBlock::PureFunctionApplication(SharedPureApplication::intern(
                "fold_pointer".into(),
                vec![PureFunctionArgument::Integer(fold.clone())],
            )),
            offset: PointerOffsetTerm::scaled_int32_node(
                MachineTerm::IntegerToMachine {
                    value: fold,
                    destination: MachineIntegerType::Int32,
                },
                4,
            ),
        };
        let shared = SharedPointerAddress::import(&address);
        for mode in MODES {
            let mut actual = BTreeSet::new();
            collect_address_variables(&shared, mode, &mut actual);
            assert_eq!(actual, native_variables(&address, mode), "{mode:?}");
        }
        let source = PointerValue::new(address, ProgramType::VoidPointer);
        let shared = SharedPointerValue::import(&source);
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
        let source = PointerValue::new(
            Pointer::symbolic(Variable(1001010)),
            ProgramType::VoidPointer,
        )
        .with_designation(Arc::new(Pointer::symbolic(Variable(1001011))))
        .with_opaque_extent(Some(Arc::new(Pointer::symbolic(Variable(1001012)))))
        .with_extent(Some(SubobjectExtent {
            start: Pointer::symbolic(Variable(1001013)),
            width: MachineTerm::Variable(Variable(1001014)),
        }));
        let shared = SharedPointerValue::import(&source);
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
        let source = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(1001015)),
        };
        let shared = SharedPointerAddress::import(&source);
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
