//! Scoped readers for common fold operands. Native leaves retain their
//! existing registry, snapshot, call-connection and capture rules.
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
                KernelTermNode::IntegerCompare { .. } | KernelTermNode::LegacyBool(_)
            )
        {
            summaries.insert(term.id(), Variables::default());
            continue;
        }
        let mut leaf_variables = BTreeSet::new();
        match term.node() {
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
            KernelTermNode::MemoryLoad { .. } => {
                collect_machine_leaf(
                    term.machine_read_leaf().expect("read node"),
                    mode,
                    &mut leaf_variables,
                    &mut SeenTerms::default(),
                );
            }
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
                KernelType::Bool => {
                    if mode == FoldVariableRead::MachineCapture
                        || (mode == FoldVariableRead::ExpressionFree
                            && collecting_connection_variables())
                    {
                        leaf_variables.insert(*variable);
                    }
                }
                _ => {}
            },
            KernelTermNode::Call { .. }
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
