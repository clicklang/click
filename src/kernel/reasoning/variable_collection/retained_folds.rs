//! Scoped readers for common fold operands. Native leaves retain their
//! existing registry, state, call-connection and capture rules.
use super::*;
use crate::kernel::{KernelFold, KernelTerm, KernelTermNode, KernelType};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum FoldVariableRead {
    IntegerFree,
    ExpressionFree,
    MachineCapture,
    IntegerBinders,
    MachineBinders,
}

impl FoldVariableRead {
    fn binder_sort(self, ty: &KernelType) -> bool {
        match self {
            Self::IntegerFree | Self::IntegerBinders => *ty == KernelType::Integer,
            Self::MachineCapture | Self::MachineBinders => matches!(ty, KernelType::Program(_)),
            Self::ExpressionFree => true,
        }
    }

    fn binders(self) -> bool {
        matches!(self, Self::IntegerBinders | Self::MachineBinders)
    }
}

type Variables = crate::persistent::PersistentSet<Variable>;

pub(super) fn union(left: &Variables, right: &Variables) -> Variables {
    let (large, small) = if left.len() >= right.len() {
        (left, right)
    } else {
        (right, left)
    };
    let mut result = large.clone();
    if small.is_empty() || large.shares_root_with(small) {
        return result;
    }
    if small.len() >= large.len().div_ceil(2) {
        // Arm scopes often remove one binder from the same shared body.
        // Structural differences skip their unchanged summary subtrees.
        for (variable, in_small) in small.diff(large) {
            if checked_collection_checkpoint() {
                break;
            }
            if in_small {
                result = result.with_value(*variable);
            }
        }
    } else {
        // A small independent contribution should visit only its own values.
        for variable in small.iter() {
            if checked_collection_checkpoint() {
                break;
            }
            result = result.with_value(*variable);
        }
    }
    result
}

pub(crate) fn collect_fold_variables(
    fold: &KernelFold,
    mode: FoldVariableRead,
    variables: &mut BTreeSet<Variable>,
) {
    // Summaries contain intrinsic free variables, before the enclosing fold
    // binds them. The same child can therefore occur outside and inside the
    // body without a context-dependent cache key or a second DAG traversal.
    let mut summaries = std::collections::HashMap::new();
    let mut outside = Variables::default();
    for child in &fold.arguments[..3] {
        let summary = common_variables(child, mode, &mut summaries);
        outside = union(&outside, &summary);
    }
    let mut body = common_variables(&fold.arguments[3], mode, &mut summaries);
    for (variable, ty) in [
        (fold.accumulator, fold.result_type().clone()),
        (fold.item, fold.index.ty()),
    ] {
        if mode.binder_sort(&ty) {
            body = if mode.binders() {
                body.with_value(variable)
            } else {
                body.without_value(&variable)
            };
        }
    }
    let result = union(&outside, &body);
    variables.extend(result.iter().copied());
}

/// Boolean roots use the same scoped child summaries as folds and matches.
/// Native compatibility leaves keep each mode's distinct dependency rules.
pub(crate) fn collect_boolean_variables(
    condition: crate::kernel::BooleanOperandView<'_>,
    mode: FoldVariableRead,
    variables: &mut BTreeSet<Variable>,
) {
    if let crate::kernel::BooleanOperandView::Shared(root) = condition {
        variables.extend(
            common_variables(root, mode, &mut Default::default())
                .iter()
                .copied(),
        );
        return;
    }
    let condition = condition.native_leaf().expect("native condition");
    let mut seen = SeenTerms::default();
    match mode {
        FoldVariableRead::IntegerFree => {
            collect_condition_integer_variables(condition, variables, &mut seen)
        }
        FoldVariableRead::ExpressionFree => {
            collect_condition_bitvector_variables(condition, variables)
        }
        FoldVariableRead::MachineCapture => {
            collect_condition_capture_variables(condition, variables, &mut seen)
        }
        FoldVariableRead::IntegerBinders | FoldVariableRead::MachineBinders => {
            let mut integers = BTreeSet::new();
            let mut machines = BTreeSet::new();
            collect_condition_binder_variables(condition, &mut integers, &mut machines, &mut seen);
            variables.extend(if mode == FoldVariableRead::IntegerBinders {
                integers
            } else {
                machines
            });
        }
    }
}

/// Algebraic argument readers count Integer carriers, including declarations;
/// an Integer match scrutinee instead asks for free Integer variables.
pub(super) fn algebraic_integer_variables(root: &KernelTerm, free: bool) -> Variables {
    let mut result = BTreeSet::new();
    let mut pending = vec![root];
    let mut seen = std::collections::HashSet::new();
    let mut native_seen = SeenTerms::default();
    let mut summaries = std::collections::HashMap::new();
    while let Some(term) = pending.pop() {
        if checked_collection_checkpoint() {
            break;
        }
        if !seen.insert(term.id()) {
            continue;
        }
        crate::instrumentation::record_deterministic_work(1);
        match term.node() {
            KernelTermNode::AlgebraicIf { arguments } => pending.extend(arguments.iter().rev()),
            KernelTermNode::AlgebraicCall(call) => {
                for argument in call.arguments.iter().rev() {
                    if matches!(argument.ty(), KernelType::Algebraic(_)) {
                        pending.push(argument);
                    } else {
                        result.extend(
                            common_variables(
                                argument,
                                FoldVariableRead::IntegerFree,
                                &mut summaries,
                            )
                            .iter()
                            .copied(),
                        );
                    }
                }
            }
            KernelTermNode::Constructor(constructor) => {
                pending.extend(constructor.fields.iter().rev())
            }
            KernelTermNode::Variable(_) if matches!(term.ty(), KernelType::Algebraic(_)) => {}
            KernelTermNode::Legacy(value) if matches!(term.ty(), KernelType::Algebraic(_)) => {
                let PureFunctionArgument::Algebraic(value) = value.value() else {
                    unreachable!()
                };
                if free {
                    collect_algebraic_free_integer_variables(value, &mut result, &mut native_seen);
                } else {
                    collect_algebraic_integer_variables(value, &mut result, &mut native_seen);
                }
            }
            _ if !free && term.ty() == &KernelType::Integer => match term.node() {
                KernelTermNode::Variable(variable) => {
                    result.insert(*variable);
                }
                KernelTermNode::Legacy(value) => collect_argument(
                    value.value(),
                    FoldVariableRead::IntegerFree,
                    &mut result,
                    &mut native_seen,
                ),
                KernelTermNode::Call { arguments, .. } => pending.extend(
                    arguments
                        .iter()
                        .rev()
                        .filter(|child| child.ty() == &KernelType::Integer),
                ),
                KernelTermNode::Fold(fold) => {
                    result.insert(fold.accumulator);
                    if fold.index.ty() == KernelType::Integer {
                        result.insert(fold.item);
                    }
                    pending.extend(fold.arguments.iter().rev());
                }
                KernelTermNode::Match(matched) => {
                    pending.extend(matched.arguments.iter().rev());
                    pending.extend(matched.arms.iter().flat_map(|arm| &arm.bindings));
                }
                _ => pending.extend(term.children().iter().rev()),
            },
            _ => result.extend(
                common_variables(term, FoldVariableRead::IntegerFree, &mut summaries)
                    .iter()
                    .copied(),
            ),
        }
    }
    let mut variables = Variables::default();
    for variable in result {
        variables = variables.with_value(variable);
    }
    variables
}

pub(super) fn common_variables(
    root: &KernelTerm,
    mode: FoldVariableRead,
    summaries: &mut std::collections::HashMap<u64, Variables>,
) -> Variables {
    let mut pending = vec![(root, false)];
    while let Some((term, finish)) = pending.pop() {
        if checked_collection_checkpoint() {
            return Variables::default();
        }
        if summaries.contains_key(&term.id()) {
            continue;
        }
        // The native Integer-free collector admits only direct Integer
        // comparisons and algebraic equality at a condition boundary. Do not
        // broaden it by descending through Boolean calls or connectives.
        if mode == FoldVariableRead::IntegerFree
            && term.ty() == &KernelType::Bool
            && !matches!(
                term.node(),
                KernelTermNode::IntegerCompare { .. }
                    | KernelTermNode::AlgebraicEqual { .. }
                    | KernelTermNode::LegacyBool(_)
            )
        {
            summaries.insert(term.id(), Variables::default());
            continue;
        }
        if mode == FoldVariableRead::IntegerFree
            && matches!(term.node(), KernelTermNode::ProgramParameter { .. })
        {
            summaries.insert(term.id(), Variables::default());
            continue;
        }
        if mode == FoldVariableRead::IntegerFree
            && matches!(
                term.node(),
                KernelTermNode::Constructor(_)
                    | KernelTermNode::AlgebraicCall(_)
                    | KernelTermNode::AlgebraicIf { .. }
            )
        {
            summaries.insert(term.id(), algebraic_integer_variables(term, false));
            continue;
        }
        let mut leaf_variables = BTreeSet::new();
        match term.node() {
            KernelTermNode::IntegerCompare { .. } if term.cached_condition_output().is_some() => {
                // This compatibility consumer already owns the exact native
                // Integer operands. Reuse their existing variable reader rather
                // than rebuilding common summaries of the same prefix.
                collect_boolean_variables(
                    crate::kernel::BooleanOperandView::Native(
                        term.cached_condition_output()
                            .expect("retained condition output"),
                    ),
                    mode,
                    &mut leaf_variables,
                );
            }
            KernelTermNode::BoolCompare { .. }
                if term.cached_condition_output().is_some_and(|condition| {
                    let ConditionTerm::Compare { left, right, .. } = condition else {
                        return false;
                    };
                    [left.as_ref(), right.as_ref()].into_iter().all(|operand| {
                        matches!(
                            operand,
                            MachineTerm::Variable(_)
                                | MachineTerm::Constant { .. }
                                | MachineTerm::MemoryLoad(..)
                        )
                    })
                }) =>
            {
                // These native scalar descriptors already carry the selected
                // read's identity and query-dependent registry connections.
                // Importing a named load as a structural read must not discard
                // that name. Arithmetic and logical DAGs keep the common walk.
                collect_boolean_variables(
                    crate::kernel::BooleanOperandView::Native(
                        term.cached_condition_output()
                            .expect("retained scalar comparison output"),
                    ),
                    mode,
                    &mut leaf_variables,
                );
            }
            KernelTermNode::Legacy(value) | KernelTermNode::LegacyBool(value) => {
                // Each opaque leaf gets its complete intrinsic answer. A seen
                // set belonging to another leaf would discard shared payload
                // variables before the enclosing body can filter its binders.
                collect_argument(
                    value.value(),
                    mode,
                    &mut leaf_variables,
                    &mut SeenTerms::default(),
                );
            }
            KernelTermNode::BoolRead(read) => {
                let (point, address) = read.parts();
                let memory = point.shared_memory();
                match mode {
                    FoldVariableRead::ExpressionFree => {
                        collect_shared_memory_bitvector_variables(memory, &mut leaf_variables);
                        super::retained_pointers::collect_address_variables_with_summaries(
                            address,
                            mode,
                            &mut leaf_variables,
                            summaries,
                        );
                        if collecting_connection_variables() {
                            collect_stored_load_connection_variables(
                                memory,
                                address.exact_cell_key(),
                                &mut leaf_variables,
                            );
                        }
                    }
                    FoldVariableRead::MachineCapture => {
                        super::retained_pointers::collect_address_variables_with_summaries(
                            address,
                            mode,
                            &mut leaf_variables,
                            summaries,
                        )
                    }
                    _ => {}
                }
            }
            KernelTermNode::PointerEqual(pair) => {
                for value in pair.arguments() {
                    for address in value.addresses() {
                        super::retained_pointers::collect_address_variables_with_summaries(
                            address,
                            mode,
                            &mut leaf_variables,
                            summaries,
                        );
                    }
                }
            }
            KernelTermNode::AddressEqual { arguments } => {
                for address in arguments {
                    super::retained_pointers::collect_address_variables_with_summaries(
                        address,
                        mode,
                        &mut leaf_variables,
                        summaries,
                    );
                }
            }
            KernelTermNode::AddressOffsetEqual { arguments } => {
                super::retained_pointers::collect_offset_variables_with_summaries(
                    arguments,
                    mode,
                    &mut leaf_variables,
                    summaries,
                );
            }
            KernelTermNode::ArrayReference { .. } => {
                collect_argument(
                    term.pointer_argument_native().expect("array descriptor"),
                    mode,
                    &mut leaf_variables,
                    &mut SeenTerms::default(),
                );
            }
            KernelTermNode::PointerRead { value, .. }
            | KernelTermNode::PointerArithmetic { value, .. }
            | KernelTermNode::PointerCall { value, .. }
            | KernelTermNode::Pointer(value) => {
                super::retained_pointers::collect_pointer_variables(
                    value,
                    mode,
                    &mut leaf_variables,
                );
            }
            KernelTermNode::IntegerAddress { address, .. } => {
                if !matches!(
                    mode,
                    FoldVariableRead::IntegerBinders | FoldVariableRead::MachineBinders
                ) {
                    super::retained_pointers::collect_address_variables_with_summaries(
                        address,
                        mode,
                        &mut leaf_variables,
                        summaries,
                    );
                }
            }
            KernelTermNode::FloatRead(read) => match mode {
                FoldVariableRead::IntegerFree | FoldVariableRead::MachineCapture => {
                    super::retained_pointers::collect_address_variables_with_summaries(
                        read.parts().1,
                        mode,
                        &mut leaf_variables,
                        summaries,
                    );
                }
                FoldVariableRead::IntegerBinders | FoldVariableRead::MachineBinders => {}
                FoldVariableRead::ExpressionFree => {
                    let (point, address) = read.parts();
                    let kind = crate::kernel::FloatOperandView::from_shared(term)
                        .expect("float read")
                        .format()
                        .load_kind();
                    collect_machine_read_variables(
                        point.shared_memory(),
                        address.exact_cell_key(),
                        kind,
                        &mut leaf_variables,
                    );
                }
            },
            KernelTermNode::AlgebraicRead(read) => match mode {
                FoldVariableRead::IntegerFree | FoldVariableRead::MachineCapture => {
                    super::retained_pointers::collect_address_variables_with_summaries(
                        read.parts().1,
                        mode,
                        &mut leaf_variables,
                        summaries,
                    );
                }
                FoldVariableRead::IntegerBinders | FoldVariableRead::MachineBinders => {}
                FoldVariableRead::ExpressionFree => {
                    let (point, address) = read.parts();
                    // The native algebraic collector uses the Bits64 read
                    // kind to follow registered origins for havoc framing.
                    collect_machine_read_variables(
                        point.shared_memory(),
                        address.exact_cell_key(),
                        LoadKind::Bits64,
                        &mut leaf_variables,
                    );
                }
            },
            KernelTermNode::MemoryLoad { address, .. } => match mode {
                FoldVariableRead::IntegerFree | FoldVariableRead::MachineCapture => {
                    super::retained_pointers::collect_address_variables_with_summaries(
                        address,
                        mode,
                        &mut leaf_variables,
                        summaries,
                    );
                }
                // Native binder readers treat reads as opaque, including their
                // addresses. The expression reader also follows memory history
                // and stored-load connections through its existing adapter.
                FoldVariableRead::IntegerBinders | FoldVariableRead::MachineBinders => {}
                FoldVariableRead::ExpressionFree => collect_machine_leaf(
                    term.machine_read_leaf().expect("read node"),
                    mode,
                    &mut leaf_variables,
                    &mut SeenTerms::default(),
                ),
            },
            KernelTermNode::Variable(variable) => match term.ty() {
                KernelType::Integer => {
                    if matches!(
                        mode,
                        FoldVariableRead::IntegerFree | FoldVariableRead::ExpressionFree
                    ) {
                        leaf_variables.insert(*variable);
                    }
                }
                KernelType::Program(_) => collect_machine_leaf(
                    &MachineTerm::Variable(*variable),
                    mode,
                    &mut leaf_variables,
                    &mut SeenTerms::default(),
                ),
                KernelType::Algebraic(_) => {
                    if mode == FoldVariableRead::ExpressionFree && collecting_connection_variables()
                    {
                        leaf_variables.insert(*variable);
                    }
                }
                KernelType::Bool
                    if (mode == FoldVariableRead::MachineCapture
                        || (mode == FoldVariableRead::ExpressionFree
                            && collecting_connection_variables())) =>
                {
                    leaf_variables.insert(*variable);
                }
                _ => {}
            },
            KernelTermNode::Call { .. } | KernelTermNode::FloatCall(_)
                if term.ty() != &KernelType::Integer
                    && mode == FoldVariableRead::ExpressionFree
                    && !collecting_connection_variables() => {}
            _ => {
                if !finish {
                    pending.push((term, true));
                    pending.extend(term.children().iter().rev().map(|child| (child, false)));
                    if let KernelTermNode::Match(matched) = term.node() {
                        pending.extend(
                            matched
                                .arms
                                .iter()
                                .flat_map(|arm| &arm.bindings)
                                .map(|child| (child, false)),
                        );
                    }
                    continue;
                }
                let mut result = Variables::default();
                if let KernelTermNode::Match(matched) = term.node() {
                    result = super::retained_matches::match_variables(matched, mode, summaries);
                } else if let KernelTermNode::Fold(fold) = term.node() {
                    for child in &fold.arguments[..3] {
                        result = union(&result, &summaries[&child.id()]);
                    }
                    let mut body = summaries[&fold.arguments[3].id()].clone();
                    for (variable, ty) in [
                        (fold.accumulator, fold.result_type().clone()),
                        (fold.item, fold.index.ty()),
                    ] {
                        if mode.binder_sort(&ty) {
                            body = if mode.binders() {
                                body.with_value(variable)
                            } else {
                                body.without_value(&variable)
                            };
                        }
                    }
                    result = union(&result, &body);
                } else {
                    for child in term.children() {
                        result = union(&result, &summaries[&child.id()]);
                    }
                }
                summaries.insert(term.id(), result);
                continue;
            }
        }
        let mut result = Variables::default();
        for variable in leaf_variables {
            result = result.with_value(variable);
        }
        summaries.insert(term.id(), result);
    }
    summaries[&root.id()].clone()
}

pub(super) fn collect_machine_leaf(
    term: &MachineTerm,
    mode: FoldVariableRead,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
) {
    match mode {
        FoldVariableRead::IntegerFree => {
            collect_bitvector_integer_variables_seen(term, variables, seen)
        }
        FoldVariableRead::ExpressionFree => collect_bitvector_variables(term, variables),
        FoldVariableRead::MachineCapture => {
            collect_bitvector_capture_variables_seen(term, variables, seen)
        }
        FoldVariableRead::IntegerBinders | FoldVariableRead::MachineBinders => {
            let mut integers = BTreeSet::new();
            let mut machines = BTreeSet::new();
            collect_bitvector_binder_variables_seen(term, &mut integers, &mut machines, seen);
            variables.extend(if mode == FoldVariableRead::IntegerBinders {
                integers
            } else {
                machines
            });
        }
    }
}

pub(super) fn collect_argument(
    argument: &PureFunctionArgument,
    mode: FoldVariableRead,
    variables: &mut BTreeSet<Variable>,
    native_seen: &mut SeenTerms,
) {
    match mode {
        FoldVariableRead::IntegerFree => {
            collect_pure_argument_integer_variables(argument, variables, native_seen)
        }
        FoldVariableRead::MachineCapture => {
            collect_capture_variables_in_pure_argument(argument, variables, native_seen)
        }
        FoldVariableRead::IntegerBinders | FoldVariableRead::MachineBinders => {
            let mut integers = BTreeSet::new();
            let mut machines = BTreeSet::new();
            collect_binder_variables_in_pure_argument(
                argument,
                &mut integers,
                &mut machines,
                native_seen,
            );
            variables.extend(if mode == FoldVariableRead::IntegerBinders {
                integers
            } else {
                machines
            });
        }
        FoldVariableRead::ExpressionFree => match argument {
            PureFunctionArgument::Integer(value) => {
                collect_shared_integer_variables(value, variables, native_seen)
            }
            PureFunctionArgument::SharedMachine(value) => {
                collect_machine_bitvector_variables(value, variables)
            }
            PureFunctionArgument::Value(value) => {
                collect_program_value_bitvector_variables(value, variables)
            }
            PureFunctionArgument::Algebraic(value) => {
                collect_algebraic_term_bitvector_variables(value, variables)
            }
            PureFunctionArgument::ArrayRef {
                memory, pointer, ..
            } => {
                collect_memory_bitvector_variables(memory, variables);
                collect_program_value_bitvector_variables(pointer, variables);
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::KernelTermImport;

    // Each answer owns its query-local frame seen set, just like the public
    // connection/frame entry points. Never share it between the two readers.
    fn condition_variables_in_scope(
        condition: crate::kernel::BooleanOperandView<'_>,
        mode: FoldVariableRead,
        connections: bool,
        frame: bool,
    ) -> BTreeSet<Variable> {
        struct Scope(bool, bool, std::collections::HashSet<(u32, u32)>);
        impl Drop for Scope {
            fn drop(&mut self) {
                CONNECTION_VARIABLES.with(|flag| flag.set(self.0));
                COLLECTING_HAVOC_RANGES.with(|flag| flag.set(self.1));
                FRAME_STATES.with(|seen| *seen.borrow_mut() = std::mem::take(&mut self.2));
            }
        }
        let _scope = Scope(
            CONNECTION_VARIABLES.with(|flag| flag.replace(connections)),
            COLLECTING_HAVOC_RANGES.with(|flag| flag.replace(frame)),
            FRAME_STATES.with(|seen| std::mem::take(&mut *seen.borrow_mut())),
        );
        let mut variables = BTreeSet::new();
        collect_boolean_variables(condition, mode, &mut variables);
        variables
    }

    #[test]
    fn retained_boolean_read_connections_use_the_exact_stored_cell() {
        use crate::kernel::BooleanOperandView;

        let _session = crate::kernel::VerificationSession::enter();
        let base = Variable(999941);
        let coordinate = Variable(999942);
        let stored = Variable(999943);
        let unrelated = Variable(999944);
        let address = Address {
            base: AddressBase::Symbolic(base),
            offset: AddressOffset::Variable(coordinate),
        };
        let memory = intern_memory(
            SymbolicMemory::new()
                .store(
                    address.clone(),
                    ProgramValue::Bool(MachineTerm::Variable(stored)),
                )
                .store(
                    Address::symbolic(base),
                    ProgramValue::Bool(MachineTerm::Variable(unrelated)),
                ),
        );
        let native = ConditionTerm::BoolLoad(ProgramPoint::at(&memory), Box::new(address));
        let root = KernelTermImport::default().condition(&native);
        let KernelTermNode::BoolRead(read) = root.node() else {
            panic!("retained Boolean read");
        };
        for (connections, frame) in [(false, false), (true, false), (true, true), (true, false)] {
            let expected = condition_variables_in_scope(
                BooleanOperandView::Native(&native),
                FoldVariableRead::ExpressionFree,
                connections,
                frame,
            );
            let actual = condition_variables_in_scope(
                BooleanOperandView::Shared(&root),
                FoldVariableRead::ExpressionFree,
                connections,
                frame,
            );
            assert_eq!(actual, expected);
            if connections {
                assert!(actual.contains(&stored));
                assert!(!actual.contains(&unrelated));
            }
        }
        let (_, work) =
            crate::instrumentation::measure_deterministic_work(|| read.parts().1.exact_cell_key());
        assert_eq!(work, 0, "the connection query prepared the exact address");
    }

    #[test]
    fn minted_scalar_comparisons_preserve_registered_load_reader_scope() {
        use crate::kernel::{
            BooleanOperandView, CompareRelation, KernelTermExport, StoredConditionTerm,
        };
        let _session = crate::kernel::VerificationSession::enter();
        let state = Variable(999951);
        let base = Variable(999952);
        let index = Variable(999953);
        let connection = Variable(999957);
        let stored_connection = Variable(999958);
        let frame_base = Variable(999954);
        let frame_index = Variable(999955);
        let pointer = Address {
            base: AddressBase::Symbolic(base),
            offset: AddressOffset::Add(
                Box::new(AddressOffset::scaled_int32_node(
                    MachineTerm::Variable(index),
                    4,
                )),
                Box::new(AddressOffset::Variable(connection)),
            ),
        };
        let memory = intern_memory(
            SymbolicMemory::new()
                .store(
                    SymbolicMemory::global_pointer("comparison-reader-history"),
                    ProgramValue::Int32(MachineTerm::Variable(state)),
                )
                .store(
                    pointer.clone(),
                    ProgramValue::Int32(MachineTerm::Variable(stored_connection)),
                ),
        );
        let writes = crate::kernel::MemoryRange::new(
            Address::symbolic(frame_base),
            MachineTerm::Variable(frame_index),
            MachineTerm::Binary {
                format: crate::kernel::MachineIntegerType::Int32,
                op: crate::kernel::MachineBinaryOp::Add,
                left: Box::new(MachineTerm::Variable(frame_index)),
                right: Box::new(1.into()),
            },
        );
        let origin = intern_memory(memory.memory().clone().with_call_memory_havoc(
            Variable(999956),
            &[writes],
            &crate::kernel::PureFactContext::new(),
            None,
        ));
        let load = crate::kernel::eval::load_variable_for_cell_with_origin(
            &memory,
            &pointer,
            LoadKind::Int32,
            4,
            &origin,
        );
        let native = [
            MachineTerm::Variable(load),
            MachineTerm::MemoryLoad(
                ProgramPoint::at(&memory),
                Box::new(pointer.clone()),
                LoadKind::Int32,
            ),
        ]
        .map(|left| ConditionTerm::Compare {
            format: crate::kernel::MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(left),
            right: Box::new(0.into()),
        });
        let stored = native
            .each_ref()
            .map(|native| StoredConditionTerm::from_minted(native.clone()));
        assert_ne!(native[0], native[1]);
        assert_ne!(
            stored[0].root(),
            stored[1].root(),
            "distinct native scalar spellings keep distinct output slots"
        );
        for (registered, (native, stored)) in
            [true, false].into_iter().zip(native.iter().zip(&stored))
        {
            let root = stored.root().expect("minted comparison root");
            assert!(matches!(root.node(), KernelTermNode::BoolCompare { .. }));
            let exports = KernelTermExport::machine_export_count();
            for (connections, frame) in [(false, false), (true, false), (true, true)] {
                for mode in [
                    FoldVariableRead::IntegerFree,
                    FoldVariableRead::ExpressionFree,
                    FoldVariableRead::MachineCapture,
                    FoldVariableRead::IntegerBinders,
                    FoldVariableRead::MachineBinders,
                ] {
                    let expected = condition_variables_in_scope(
                        BooleanOperandView::Native(native),
                        mode,
                        connections,
                        frame,
                    );
                    if mode == FoldVariableRead::ExpressionFree {
                        assert!(expected.contains(&base));
                        assert!(expected.contains(&index));
                        assert_eq!(
                            expected.contains(&state),
                            !connections,
                            "registered={registered}, connections={connections}, frame={frame}, expected={expected:?}"
                        );
                        assert!(expected.contains(&stored_connection));
                        assert_eq!(expected.contains(&connection), connections);
                        assert_eq!(expected.contains(&load), registered);
                        if frame {
                            assert!(expected.contains(&frame_base));
                            assert!(expected.contains(&frame_index));
                        }
                    } else if mode == FoldVariableRead::MachineCapture {
                        assert!(expected.contains(&base));
                        assert!(expected.contains(&index));
                        assert_eq!(expected.contains(&load), registered);
                        assert!(!expected.contains(&state));
                    } else {
                        assert!(expected.is_empty());
                    }
                    let actual = condition_variables_in_scope(
                        BooleanOperandView::Shared(root),
                        mode,
                        connections,
                        frame,
                    );
                    assert_eq!(
                        actual, expected,
                        "registered={registered}, mode={mode:?}, connections={connections}, frame={frame}"
                    );
                }
            }
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }

    fn native_variables(term: &IntegerTerm, mode: FoldVariableRead) -> BTreeSet<Variable> {
        let mut result = BTreeSet::new();
        match mode {
            FoldVariableRead::IntegerFree => collect_integer_free_variables(term, &mut result),
            FoldVariableRead::ExpressionFree => collect_integer_variables(term, &mut result),
            FoldVariableRead::MachineCapture => {
                collect_integer_capture_bitvector_variables(term, &mut result)
            }
            FoldVariableRead::IntegerBinders | FoldVariableRead::MachineBinders => {
                let mut integers = BTreeSet::new();
                let mut machines = BTreeSet::new();
                collect_integer_binder_variables(term, &mut integers, &mut machines);
                result = if mode == FoldVariableRead::IntegerBinders {
                    integers
                } else {
                    machines
                };
            }
        }
        result
    }

    #[test]
    fn float_readers_preserve_state_address_and_native_collection_modes() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = intern_memory(
            SymbolicMemory::new()
                .with_block("float-read-history", 4)
                .store(
                    SymbolicMemory::global_pointer("float-read-history"),
                    ProgramValue::Int32(MachineTerm::Variable(Variable(999811))),
                ),
        );
        let pointer = Address {
            base: AddressBase::Symbolic(Variable(999812)),
            offset: AddressOffset::scaled_int32_node(MachineTerm::Variable(Variable(999813)), 4),
        };
        for format in [
            crate::kernel::KernelFloatType::Float32,
            crate::kernel::KernelFloatType::Float64,
        ] {
            let argument = PureFunctionArgument::Value(format.value(MachineTerm::MemoryLoad(
                ProgramPoint::at(&memory),
                Box::new(pointer.clone()),
                format.load_kind(),
            )));
            let root = KernelTermImport::default().argument(&argument);
            assert!(matches!(root.node(), KernelTermNode::FloatRead(_)));
            for mode in [
                FoldVariableRead::IntegerFree,
                FoldVariableRead::ExpressionFree,
                FoldVariableRead::MachineCapture,
                FoldVariableRead::IntegerBinders,
                FoldVariableRead::MachineBinders,
            ] {
                let mut expected = BTreeSet::new();
                collect_argument(&argument, mode, &mut expected, &mut SeenTerms::default());
                let actual = common_variables(&root, mode, &mut Default::default())
                    .iter()
                    .copied()
                    .collect::<BTreeSet<_>>();
                assert_eq!(actual, expected, "{format:?} {mode:?}");
            }
            assert!(!root.has_cached_native_argument());
        }
    }

    #[test]
    fn float_arithmetic_readers_preserve_all_native_collection_modes() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [
            crate::kernel::KernelFloatType::Float32,
            crate::kernel::KernelFloatType::Float64,
        ] {
            let left = Box::new(MachineTerm::Variable(Variable(999933)));
            let right = Box::new(MachineTerm::MemoryLoad(
                ProgramPoint::at(&(intern_memory(SymbolicMemory::new()))),
                Box::new(Address::symbolic(Variable(999934))),
                format.load_kind(),
            ));
            let native = match format {
                crate::kernel::KernelFloatType::Float32 => {
                    MachineTerm::Float32Negate(Box::new(MachineTerm::Float32Binary {
                        operator: crate::kernel::FloatBinaryOperator::Divide,
                        left,
                        right,
                    }))
                }
                crate::kernel::KernelFloatType::Float64 => {
                    MachineTerm::Float64Negate(Box::new(MachineTerm::Float64Binary {
                        operator: crate::kernel::FloatBinaryOperator::Divide,
                        left,
                        right,
                    }))
                }
            };
            let argument = PureFunctionArgument::Value(format.value(native));
            let root = KernelTermImport::default().argument(&argument);
            for mode in [
                FoldVariableRead::IntegerFree,
                FoldVariableRead::ExpressionFree,
                FoldVariableRead::MachineCapture,
                FoldVariableRead::IntegerBinders,
                FoldVariableRead::MachineBinders,
            ] {
                let mut expected = BTreeSet::new();
                collect_argument(&argument, mode, &mut expected, &mut SeenTerms::default());
                let actual = common_variables(&root, mode, &mut Default::default())
                    .iter()
                    .copied()
                    .collect::<BTreeSet<_>>();
                assert_eq!(actual, expected, "{format:?} {mode:?}");
            }
        }
    }

    #[test]
    fn float_conversion_readers_preserve_all_native_collection_modes() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [
            crate::kernel::KernelFloatType::Float32,
            crate::kernel::KernelFloatType::Float64,
        ] {
            let left = Box::new(MachineTerm::Variable(Variable(999933)));
            let right = Box::new(MachineTerm::MemoryLoad(
                ProgramPoint::at(&(intern_memory(SymbolicMemory::new()))),
                Box::new(Address::symbolic(Variable(999934))),
                format.load_kind(),
            ));
            let native = match format {
                crate::kernel::KernelFloatType::Float32 => {
                    MachineTerm::Float32Negate(Box::new(MachineTerm::Float32Binary {
                        operator: crate::kernel::FloatBinaryOperator::Divide,
                        left,
                        right,
                    }))
                }
                crate::kernel::KernelFloatType::Float64 => {
                    MachineTerm::Float64Negate(Box::new(MachineTerm::Float64Binary {
                        operator: crate::kernel::FloatBinaryOperator::Divide,
                        left,
                        right,
                    }))
                }
            };
            let (name, target) = match format {
                crate::kernel::KernelFloatType::Float32 => (
                    "c_float32_to_float64",
                    crate::kernel::KernelFloatType::Float64,
                ),
                crate::kernel::KernelFloatType::Float64 => (
                    "c_float64_to_float32",
                    crate::kernel::KernelFloatType::Float32,
                ),
            };
            let integer = MachineTerm::opaque_conversion(
                format!(
                    "c_{}_to_int32",
                    crate::kernel::program_type_spelling(format.program_type())
                ),
                native.clone(),
            );
            let native = MachineTerm::opaque_conversion(name, native);
            for argument in [
                PureFunctionArgument::Value(target.value(native)),
                PureFunctionArgument::Value(ProgramValue::Int32(integer)),
            ] {
                let root = KernelTermImport::default().argument(&argument);
                for mode in [
                    FoldVariableRead::IntegerFree,
                    FoldVariableRead::ExpressionFree,
                    FoldVariableRead::MachineCapture,
                    FoldVariableRead::IntegerBinders,
                    FoldVariableRead::MachineBinders,
                ] {
                    let mut expected = BTreeSet::new();
                    collect_argument(&argument, mode, &mut expected, &mut SeenTerms::default());
                    let actual = common_variables(&root, mode, &mut Default::default())
                        .iter()
                        .copied()
                        .collect::<BTreeSet<_>>();
                    assert_eq!(actual, expected, "{format:?} {mode:?}");
                }
            }
        }
    }

    #[test]
    fn float_atom_readers_preserve_all_native_collection_modes() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [
            crate::kernel::KernelFloatType::Float32,
            crate::kernel::KernelFloatType::Float64,
        ] {
            let constant = match format {
                crate::kernel::KernelFloatType::Float32 => MachineTerm::constant(0),
                crate::kernel::KernelFloatType::Float64 => MachineTerm::uint64_constant(0),
            };
            for native in [MachineTerm::Variable(Variable(999803)), constant] {
                let argument = PureFunctionArgument::Value(format.value(native));
                let root = KernelTermImport::default().argument(&argument);
                for mode in [
                    FoldVariableRead::IntegerFree,
                    FoldVariableRead::ExpressionFree,
                    FoldVariableRead::MachineCapture,
                    FoldVariableRead::IntegerBinders,
                    FoldVariableRead::MachineBinders,
                ] {
                    let mut expected = BTreeSet::new();
                    collect_argument(&argument, mode, &mut expected, &mut SeenTerms::default());
                    let actual = common_variables(&root, mode, &mut Default::default())
                        .iter()
                        .copied()
                        .collect::<BTreeSet<_>>();
                    assert_eq!(actual, expected, "{format:?} {mode:?}");
                }
            }
        }
    }

    #[test]
    fn algebraic_constructor_readers_keep_free_and_carrier_variable_rules() {
        let _session = crate::kernel::VerificationSession::enter();
        let mut native = KernelMatch::test_scrutinee(vec![AlgebraicValueType::Integer]);
        native.node = AlgebraicTermNode::Constructor {
            variant: "Arm".into(),
            fields: vec![AlgebraicValue::Integer(IntegerTerm::RangeFold {
                index: IntegerRangeFoldIndex::Integer {
                    start: IntegerTerm::constant_i64(0).into(),
                    end: IntegerTerm::Variable(Variable(999611)).into(),
                },
                initial: IntegerTerm::Variable(Variable(999612)).into(),
                accumulator: Variable(999613),
                item: Variable(999614),
                body: IntegerTerm::Variable(Variable(999613)).into(),
            })],
        };
        let other = AlgebraicTerm {
            algebraic_type: native.algebraic_type.clone(),
            node: AlgebraicTermNode::Variable(Variable(999615)),
        };
        let condition = ConditionTerm::AlgebraicEqual(Box::new(native.clone()), Box::new(other));
        let guard = KernelTermImport::default().condition(&condition);
        let root = KernelTermImport::default().algebraic(&native);
        let argument = PureFunctionArgument::Algebraic(native.clone());
        for mode in [
            FoldVariableRead::IntegerFree,
            FoldVariableRead::ExpressionFree,
            FoldVariableRead::MachineCapture,
            FoldVariableRead::IntegerBinders,
            FoldVariableRead::MachineBinders,
        ] {
            let mut expected = BTreeSet::new();
            collect_argument(&argument, mode, &mut expected, &mut SeenTerms::default());
            let actual = common_variables(&root, mode, &mut Default::default())
                .iter()
                .copied()
                .collect::<BTreeSet<_>>();
            assert_eq!(actual, expected, "{mode:?}");
            let mut expected = BTreeSet::new();
            let mut actual = BTreeSet::new();
            collect_boolean_variables(
                crate::kernel::BooleanOperandView::Native(&condition),
                mode,
                &mut expected,
            );
            collect_boolean_variables(
                crate::kernel::BooleanOperandView::Shared(&guard),
                mode,
                &mut actual,
            );
            assert_eq!(actual, expected, "algebraic equality {mode:?}");
        }
        let mut expected = BTreeSet::new();
        collect_algebraic_free_integer_variables(&native, &mut expected, &mut SeenTerms::default());
        let actual = algebraic_integer_variables(&root, true)
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        assert_eq!(actual, expected);
        assert!(!actual.contains(&Variable(999613)));
        assert!(algebraic_integer_variables(&root, false).contains(&Variable(999613)));
    }

    #[test]
    fn algebraic_call_readers_preserve_argument_and_carrier_modes() {
        let _session = crate::kernel::VerificationSession::enter();
        let fold = IntegerTerm::RangeFold {
            index: IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::Variable(Variable(999711)).into(),
            },
            initial: IntegerTerm::Variable(Variable(999712)).into(),
            accumulator: Variable(999713),
            item: Variable(999714),
            body: IntegerTerm::Variable(Variable(999713)).into(),
        };
        let mut nested = KernelMatch::test_scrutinee(vec![AlgebraicValueType::Integer]);
        nested.node = AlgebraicTermNode::Constructor {
            variant: "Arm".into(),
            fields: vec![AlgebraicValue::Integer(fold.clone())],
        };
        let native = AlgebraicTerm {
            algebraic_type: nested.algebraic_type.clone(),
            node: AlgebraicTermNode::PureFunctionApplication {
                name: "algebraic_reader_modes".into(),
                arguments: vec![
                    PureFunctionArgument::Integer(fold.into()),
                    PureFunctionArgument::Algebraic(nested),
                    PureFunctionArgument::Value(ProgramValue::Int32(MachineTerm::Variable(
                        Variable(999715),
                    ))),
                    PureFunctionArgument::SharedMachine(SharedMachineIntegerTerm::intern(
                        MachineIntegerType::Int32,
                        MachineTerm::Variable(Variable(999716)),
                    )),
                ],
            },
        };
        let conditional = AlgebraicTerm {
            algebraic_type: native.algebraic_type.clone(),
            node: AlgebraicTermNode::If {
                condition: Box::new(ConditionTerm::integer_equal(
                    IntegerTerm::var(Variable(999717)),
                    IntegerTerm::constant_i64(0),
                )),
                then_term: Box::new(native.clone()),
                else_term: Box::new(KernelMatch::test_scrutinee(vec![
                    AlgebraicValueType::Integer,
                ])),
            },
        };
        let read = AlgebraicTerm {
            algebraic_type: crate::kernel::TypeParameterName::intern("AlgebraicReaderT")
                .algebraic_type(),
            node: AlgebraicTermNode::MemoryLoad {
                point: crate::kernel::ProgramPoint::at(&crate::kernel::intern_memory(
                    SymbolicMemory::new()
                        .with_block("algebraic-reader", 8)
                        .store(
                            SymbolicMemory::global_pointer("algebraic-reader"),
                            ProgramValue::UInt64(MachineTerm::Variable(Variable(999741))),
                        ),
                )),
                pointer: Box::new(Address {
                    base: AddressBase::Symbolic(Variable(999742)),
                    offset: AddressOffset::scaled_int32_node(
                        MachineTerm::Variable(Variable(999743)),
                        4,
                    ),
                }),
            },
        };
        for native in [native, conditional, read] {
            let root = KernelTermImport::default().algebraic(&native);
            struct Restore(bool);
            impl Drop for Restore {
                fn drop(&mut self) {
                    CONNECTION_VARIABLES.with(|flag| flag.set(self.0));
                }
            }
            for connection in [false, true, false] {
                let _restore = Restore(CONNECTION_VARIABLES.with(|flag| flag.replace(connection)));
                for mode in [
                    FoldVariableRead::IntegerFree,
                    FoldVariableRead::ExpressionFree,
                    FoldVariableRead::MachineCapture,
                    FoldVariableRead::IntegerBinders,
                    FoldVariableRead::MachineBinders,
                ] {
                    let mut expected = BTreeSet::new();
                    collect_argument(
                        &PureFunctionArgument::Algebraic(native.clone()),
                        mode,
                        &mut expected,
                        &mut SeenTerms::default(),
                    );
                    let actual = common_variables(&root, mode, &mut Default::default())
                        .iter()
                        .copied()
                        .collect::<BTreeSet<_>>();
                    assert_eq!(actual, expected, "mode={mode:?} connection={connection}");
                }
                let mut expected = BTreeSet::new();
                collect_algebraic_free_integer_variables(
                    &native,
                    &mut expected,
                    &mut SeenTerms::default(),
                );
                assert_eq!(
                    algebraic_integer_variables(&root, true)
                        .iter()
                        .copied()
                        .collect::<BTreeSet<_>>(),
                    expected
                );
            }
        }
    }

    #[test]
    fn retained_boolean_call_arguments_preserve_dependency_modes() {
        use crate::kernel::BooleanOperandView as V;
        let _session = crate::kernel::VerificationSession::enter();
        let argument = KernelTermImport::default().condition(&ConditionTerm::BoolIf {
            condition: Box::new(ConditionTerm::Variable(Variable(999560))),
            then_condition: Box::new(ConditionTerm::IntegerEqual(
                IntegerTerm::Variable(Variable(999561)).into(),
                IntegerTerm::Variable(Variable(999562)).into(),
            )),
            else_condition: Box::new(ConditionTerm::BoolLoad(
                crate::kernel::ProgramPoint::at(&crate::kernel::intern_memory(
                    SymbolicMemory::new(),
                )),
                Box::new(Address::symbolic(Variable(999563))),
            )),
        });
        let application = SharedPureApplication::intern(
            "boolean_dependency_handoff".into(),
            vec![argument.boolean_argument_native().unwrap().clone()],
        );
        let common =
            KernelTermImport::default().boolean_call_with_retained(&application, &[Some(argument)]);
        let native = ConditionTerm::BoolApplication(application);
        struct Restore(bool);
        impl Drop for Restore {
            fn drop(&mut self) {
                CONNECTION_VARIABLES.with(|flag| flag.set(self.0));
            }
        }
        for connection in [false, true, false] {
            let _restore = Restore(CONNECTION_VARIABLES.with(|flag| flag.replace(connection)));
            for mode in [
                FoldVariableRead::IntegerFree,
                FoldVariableRead::ExpressionFree,
                FoldVariableRead::MachineCapture,
                FoldVariableRead::IntegerBinders,
                FoldVariableRead::MachineBinders,
            ] {
                let mut expected = BTreeSet::new();
                let mut actual = BTreeSet::new();
                collect_boolean_variables(V::Native(&native), mode, &mut expected);
                collect_boolean_variables(V::Shared(&common), mode, &mut actual);
                assert_eq!(actual, expected, "mode={mode:?} connection={connection}");
            }
        }
    }

    #[test]
    fn standalone_boolean_dependencies_preserve_collection_modes() {
        use crate::kernel::BooleanOperandView as V;
        let comparison = ConditionTerm::IntegerEqual(
            IntegerTerm::Variable(Variable(970_001)).into(),
            IntegerTerm::Variable(Variable(970_002)).into(),
        );
        for source in [
            ConditionTerm::BoolLoad(
                crate::kernel::ProgramPoint::at(&crate::kernel::intern_memory(
                    crate::kernel::SymbolicMemory::new()
                        .with_block("bool-dependencies", 4)
                        .store(
                            crate::kernel::SymbolicMemory::global_pointer("bool-dependencies"),
                            ProgramValue::Int32(MachineTerm::Variable(Variable(970_030))),
                        ),
                )),
                Box::new(Address {
                    base: AddressBase::Symbolic(Variable(970_031)),
                    offset: AddressOffset::scaled_int32_node(
                        MachineTerm::Variable(Variable(970_032)),
                        4,
                    ),
                }),
            ),
            ConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: crate::kernel::OverflowOperation::Add,
                left: Box::new(MachineTerm::IntegerToMachine {
                    value: IntegerTerm::Variable(Variable(970_020)).into(),
                    destination: MachineIntegerType::Int32,
                }),
                right: Box::new(MachineTerm::Variable(Variable(970_021))),
            },
            ConditionTerm::PointerEqual(
                Box::new(
                    Pointer::new(
                        Address::symbolic(Variable(970_010)),
                        ProgramType::Int32Pointer,
                    )
                    .with_bounds(Some(SubobjectBounds {
                        start: Address::symbolic(Variable(970_011)),
                        width: MachineTerm::Variable(Variable(970_012)),
                    })),
                ),
                Box::new(Pointer::new(Address::null(), ProgramType::Int32Pointer)),
            ),
            ConditionTerm::AddressOffsetEqual(
                Box::new(AddressOffset::Add(
                    Box::new(AddressOffset::Variable(Variable(970_005))),
                    Box::new(AddressOffset::scaled_int32_node(
                        MachineTerm::IntegerToMachine {
                            value: IntegerTerm::Variable(Variable(970_006)).into(),
                            destination: MachineIntegerType::Int32,
                        },
                        4,
                    )),
                )),
                Box::new(AddressOffset::scaled_int64_node(
                    MachineTerm::Variable(Variable(970_007)),
                    8,
                    true,
                )),
            ),
            ConditionTerm::AddressEqual(
                Box::new(Address {
                    base: AddressBase::PureFunctionApplication(SharedPureApplication::intern(
                        "raw_pointer_dependency".into(),
                        vec![PureFunctionArgument::Integer(
                            IntegerTerm::Variable(Variable(970_008)).into(),
                        )],
                    )),
                    offset: AddressOffset::scaled_int32_node(
                        MachineTerm::Variable(Variable(970_009)),
                        4,
                    ),
                }),
                Box::new(Address {
                    base: AddressBase::ExternalObject(Variable(970_010)),
                    offset: AddressOffset::scaled_int64_node(
                        MachineTerm::Variable(Variable(970_011)),
                        8,
                        false,
                    ),
                }),
            ),
            comparison.clone(),
            ConditionTerm::BoolIf {
                condition: Box::new(ConditionTerm::Variable(Variable(970_003))),
                then_condition: Box::new(comparison),
                else_condition: Box::new(ConditionTerm::BoolApplication(
                    SharedPureApplication::intern(
                        "boolean_dependency_call".into(),
                        vec![PureFunctionArgument::Value(ProgramValue::Int32(
                            MachineTerm::Variable(Variable(970_004)),
                        ))],
                    ),
                )),
            },
        ] {
            let root = KernelTermImport::default().condition(&source);
            for mode in [
                FoldVariableRead::IntegerFree,
                FoldVariableRead::ExpressionFree,
                FoldVariableRead::MachineCapture,
                FoldVariableRead::IntegerBinders,
                FoldVariableRead::MachineBinders,
            ] {
                let mut native = BTreeSet::new();
                let mut common = BTreeSet::new();
                collect_boolean_variables(V::Native(&source), mode, &mut native);
                collect_boolean_variables(V::Shared(&root), mode, &mut common);
                assert_eq!(common, native, "{mode:?}");
            }
        }
    }

    #[test]
    fn retained_fold_condition_readers_preserve_each_collection_mode() {
        let integer = |n| SharedIntegerTerm::from(IntegerTerm::Variable(Variable(n)));
        let comparison = ConditionTerm::IntegerEqual(integer(62), integer(63));
        for (index, condition) in [
            ConditionTerm::Variable(Variable(61)),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(MachineTerm::IntegerToMachine {
                    value: integer(62),
                    destination: MachineIntegerType::Int32,
                }),
                right: Box::new(MachineTerm::Variable(Variable(63))),
            },
            ConditionTerm::BoolEqual(
                Box::new(comparison.clone()),
                Box::new(ConditionTerm::Constant(true)),
            ),
            comparison,
        ]
        .into_iter()
        .enumerate()
        {
            let source = IntegerTerm::RangeFold {
                index: IntegerRangeFoldIndex::Integer {
                    start: IntegerTerm::constant_i64(0).into(),
                    end: integer(60),
                },
                initial: IntegerTerm::constant_i64(0).into(),
                accumulator: Variable(64),
                item: Variable(65),
                body: IntegerTerm::If {
                    condition: Box::new(condition),
                    then_term: IntegerTerm::constant_i64(0).into(),
                    else_term: IntegerTerm::constant_i64(1).into(),
                }
                .into(),
            };
            let common =
                KernelFold::import_integer(&mut KernelTermImport::default(), &source).unwrap();
            for mode in [
                FoldVariableRead::IntegerFree,
                FoldVariableRead::ExpressionFree,
                FoldVariableRead::MachineCapture,
                FoldVariableRead::IntegerBinders,
                FoldVariableRead::MachineBinders,
            ] {
                let mut actual = BTreeSet::new();
                collect_fold_variables(&common, mode, &mut actual);
                assert_eq!(
                    actual,
                    native_variables(&source, mode),
                    "case={index}, mode={mode:?}"
                );
                if index == 0 && mode == FoldVariableRead::MachineCapture {
                    assert!(actual.contains(&Variable(61)));
                }
                if mode == FoldVariableRead::IntegerFree {
                    assert_eq!(actual.contains(&Variable(62)), index == 3);
                }
            }
        }
    }

    #[test]
    fn retained_machine_fold_readers_preserve_carrier_specific_scope() {
        let body = MachineTerm::Binary {
            format: MachineIntegerType::Int32,
            op: MachineBinaryOp::Add,
            left: Box::new(MachineTerm::Variable(Variable(51))),
            right: Box::new(MachineTerm::IntegerToMachine {
                value: IntegerTerm::Variable(Variable(51)).into(),
                destination: MachineIntegerType::Int32,
            }),
        };
        let source = MachineTerm::RangeFold {
            start: Box::new(MachineTerm::Variable(Variable(52))),
            end: Box::new(MachineTerm::Variable(Variable(53))),
            initial: Box::new(MachineTerm::Variable(Variable(51))),
            accumulator: Variable(51),
            item: Variable(52),
            body: Box::new(body),
        };
        let common = KernelFold::import_machine(&mut KernelTermImport::default(), &source).unwrap();
        for mode in [
            FoldVariableRead::IntegerFree,
            FoldVariableRead::ExpressionFree,
            FoldVariableRead::MachineCapture,
            FoldVariableRead::IntegerBinders,
            FoldVariableRead::MachineBinders,
        ] {
            let mut expected = BTreeSet::new();
            collect_machine_leaf(&source, mode, &mut expected, &mut SeenTerms::default());
            let mut actual = BTreeSet::new();
            collect_fold_variables(&common, mode, &mut actual);
            assert_eq!(actual, expected, "mode={mode:?}");
            if mode == FoldVariableRead::IntegerFree {
                assert_eq!(actual, BTreeSet::from([Variable(51)]));
            }
            if mode == FoldVariableRead::MachineBinders {
                assert_eq!(actual, BTreeSet::from([Variable(51), Variable(52)]));
            }
        }
    }

    #[test]
    fn retained_fold_collectors_keep_call_connection_modes_query_local() {
        let value = |n| {
            PureFunctionArgument::Value(ProgramValue::Int32(MachineTerm::Variable(Variable(n))))
        };
        let integer = |n| PureFunctionArgument::Integer(IntegerTerm::Variable(Variable(n)).into());
        let source = IntegerTerm::RangeFold {
            index: IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::Variable(Variable(30)).into(),
            },
            initial: IntegerTerm::Variable(Variable(11)).into(),
            accumulator: Variable(11),
            item: Variable(12),
            body: IntegerTerm::If {
                condition: Box::new(ConditionTerm::BoolApplication(
                    SharedPureApplication::intern("guard".into(), vec![value(31), integer(32)]),
                )),
                then_term: IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                    "result".into(),
                    vec![value(33), integer(34)],
                ))
                .into(),
                else_term: IntegerTerm::Variable(Variable(11)).into(),
            }
            .into(),
        };
        let common = KernelFold::import_integer(&mut KernelTermImport::default(), &source).unwrap();
        struct Restore(bool);
        impl Drop for Restore {
            fn drop(&mut self) {
                CONNECTION_VARIABLES.with(|flag| flag.set(self.0));
            }
        }
        for connection in [false, true, false] {
            let _restore = Restore(CONNECTION_VARIABLES.with(|flag| flag.replace(connection)));
            for mode in [
                FoldVariableRead::IntegerFree,
                FoldVariableRead::ExpressionFree,
                FoldVariableRead::MachineCapture,
                FoldVariableRead::IntegerBinders,
                FoldVariableRead::MachineBinders,
            ] {
                let mut actual = BTreeSet::new();
                collect_fold_variables(&common, mode, &mut actual);
                assert_eq!(
                    actual,
                    native_variables(&source, mode),
                    "mode={mode:?}, connection={connection}"
                );
                if mode == FoldVariableRead::ExpressionFree {
                    assert_eq!(actual.contains(&Variable(31)), connection);
                    assert!(actual.contains(&Variable(33)));
                }
            }
        }
    }

    #[test]
    fn retained_fold_collectors_preserve_scopes_carriers_and_nested_binders() {
        let variable = |n| SharedIntegerTerm::from(IntegerTerm::Variable(Variable(n)));
        let nested: SharedIntegerTerm = IntegerTerm::RangeFold {
            index: IntegerRangeFoldIndex::Integer {
                start: variable(11),
                end: variable(12),
            },
            initial: variable(13),
            accumulator: Variable(11),
            item: Variable(14),
            body: IntegerTerm::Add(variable(11), variable(14)).into(),
        }
        .into();
        for index in [
            IntegerRangeFoldIndex::Integer {
                start: variable(11),
                end: variable(12),
            },
            IntegerRangeFoldIndex::Int32 {
                start: SharedIntegerRangeEndpoint::intern(MachineTerm::Variable(Variable(11))),
                end: SharedIntegerRangeEndpoint::intern(MachineTerm::Variable(Variable(12))),
            },
            IntegerRangeFoldIndex::UInt64 {
                start: SharedIntegerRangeEndpoint::intern(MachineTerm::Variable(Variable(11))),
                end: SharedIntegerRangeEndpoint::intern(MachineTerm::Variable(Variable(12))),
            },
        ] {
            let source = IntegerTerm::RangeFold {
                index,
                initial: variable(11),
                accumulator: Variable(11),
                item: Variable(12),
                body: IntegerTerm::Add(
                    nested.clone(),
                    IntegerTerm::Add(
                        variable(12),
                        IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                            MachineIntegerType::Int32,
                            MachineTerm::Variable(Variable(12)),
                        ))
                        .into(),
                    )
                    .into(),
                )
                .into(),
            };
            let common =
                KernelFold::import_integer(&mut KernelTermImport::default(), &source).unwrap();
            for mode in [
                FoldVariableRead::IntegerFree,
                FoldVariableRead::ExpressionFree,
                FoldVariableRead::MachineCapture,
                FoldVariableRead::IntegerBinders,
                FoldVariableRead::MachineBinders,
            ] {
                let mut actual = BTreeSet::new();
                collect_fold_variables(&common, mode, &mut actual);
                assert_eq!(
                    actual,
                    native_variables(&source, mode),
                    "mode={mode:?}, range={:?}",
                    common.index
                );
            }
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/reasoning/variable_collection/retained_folds.rs");
}

/// The native result carrier is a shallow compatibility reading; select its
/// common fold once before walking the scoped children.
pub(super) fn collect_native_fold_variables(
    term: &IntegerTerm,
    mode: FoldVariableRead,
    variables: &mut BTreeSet<Variable>,
) -> bool {
    if !matches!(
        term,
        IntegerTerm::RangeFold { .. } | IntegerTerm::AlgebraicMatch { .. }
    ) {
        return false;
    }
    let root = crate::kernel::KernelTermImport::default().integer(&term.clone().into());
    match root.node() {
        KernelTermNode::Fold(fold) => collect_fold_variables(fold, mode, variables),
        KernelTermNode::Match(matched) => {
            super::retained_matches::collect_match_variables(matched, mode, variables)
        }
        _ => unreachable!("migrated Integer scope"),
    }
    true
}

#[cfg(test)]
mod float_call_tests {
    use super::*;
    #[test]
    fn float_calls_keep_native_variable_reader_policies() {
        let _session = crate::kernel::VerificationSession::enter();
        let native = MachineTerm::ClickFunctionApplication {
            name: "float_variables".into(),
            arguments: vec![
                PureFunctionArgument::Integer(IntegerTerm::Variable(Variable(1008205)).into()),
                PureFunctionArgument::Value(ProgramValue::Int32(MachineTerm::Variable(Variable(
                    1008206,
                )))),
                PureFunctionArgument::Value(ProgramValue::Float64(
                    MachineTerm::ClickFunctionApplication {
                        name: "inner".into(),
                        arguments: vec![PureFunctionArgument::Value(ProgramValue::Float64(
                            MachineTerm::Variable(Variable(1008207)),
                        ))],
                    },
                )),
                PureFunctionArgument::Value(ProgramValue::Bool(MachineTerm::Variable(Variable(
                    1008208,
                )))),
            ],
        };
        let root = crate::kernel::KernelTermImport::default()
            .float(crate::kernel::KernelFloatType::Float64, &native);
        for connection in [false, true] {
            struct Restore(bool);
            impl Drop for Restore {
                fn drop(&mut self) {
                    CONNECTION_VARIABLES.with(|flag| flag.set(self.0));
                }
            }
            let _connection = Restore(CONNECTION_VARIABLES.with(|flag| flag.replace(connection)));
            for mode in [
                FoldVariableRead::IntegerFree,
                FoldVariableRead::ExpressionFree,
                FoldVariableRead::MachineCapture,
                FoldVariableRead::IntegerBinders,
                FoldVariableRead::MachineBinders,
            ] {
                let mut expected = BTreeSet::new();
                collect_machine_leaf(&native, mode, &mut expected, &mut SeenTerms::default());
                let actual = common_variables(&root, mode, &mut Default::default())
                    .iter()
                    .copied()
                    .collect::<BTreeSet<_>>();
                assert_eq!(actual, expected, "mode={mode:?} connection={connection}");
            }
        }
    }
}

#[cfg(test)]
mod mixed_argument_tests {
    use super::*;
    #[test]
    fn mixed_arguments_keep_all_native_variable_reader_policies() {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = TypeParameterName::intern("MixedVariableT").algebraic_type();
        let value = AlgebraicTerm {
            algebraic_type: ty,
            node: AlgebraicTermNode::PureFunctionApplication {
                name: "mixed_variables".into(),
                arguments: vec![
                    PureFunctionArgument::Integer(IntegerTerm::Variable(Variable(1008510)).into()),
                    PureFunctionArgument::Value(ProgramValue::Float64(MachineTerm::Variable(
                        Variable(1008511),
                    ))),
                ],
            },
        };
        let pointer = ProgramValue::Pointer(Pointer::new(
            Address::symbolic(Variable(1008512)),
            ProgramType::Int32Pointer,
        ));
        let arguments = [
            PureFunctionArgument::Algebraic(value.clone()),
            PureFunctionArgument::Value(ProgramValue::Parameter(Box::new(value))),
            PureFunctionArgument::Value(pointer.clone()),
            PureFunctionArgument::ArrayRef {
                memory: SymbolicMemory::new(),
                pointer,
                element_type: ProgramType::Int32,
            },
            PureFunctionArgument::Value(ProgramValue::Bool(MachineTerm::bool_cast(
                MachineIntegerType::UInt8,
                ConditionTerm::bool_application(
                    "bool_variables",
                    vec![PureFunctionArgument::Integer(
                        IntegerTerm::Variable(Variable(1008513)).into(),
                    )],
                ),
            ))),
        ];
        for connection in [false, true] {
            struct Restore(bool);
            impl Drop for Restore {
                fn drop(&mut self) {
                    CONNECTION_VARIABLES.with(|flag| flag.set(self.0));
                }
            }
            let _restore = Restore(CONNECTION_VARIABLES.with(|flag| flag.replace(connection)));
            for argument in &arguments {
                let root = crate::kernel::KernelTermImport::default().argument(argument);
                for mode in [
                    FoldVariableRead::IntegerFree,
                    FoldVariableRead::ExpressionFree,
                    FoldVariableRead::MachineCapture,
                    FoldVariableRead::IntegerBinders,
                    FoldVariableRead::MachineBinders,
                ] {
                    let mut expected = BTreeSet::new();
                    collect_argument(argument, mode, &mut expected, &mut SeenTerms::default());
                    let actual = common_variables(&root, mode, &mut Default::default())
                        .iter()
                        .copied()
                        .collect::<BTreeSet<_>>();
                    assert_eq!(
                        actual, expected,
                        "mode={mode:?} connection={connection} argument={argument:?}"
                    );
                }
            }
        }
    }
}
