//! Common/native fold keys share the same scoped child walker and refusal rules.
use super::*;
use crate::kernel::{
    KernelFold, KernelFoldIndex, KernelIntegerOperator, KernelTerm, KernelTermExport,
    KernelTermNode, KernelType, MachineOperandView,
};

pub(super) fn bindings() -> AlphaBindings {
    AlphaBindings {
        integer: BTreeMap::new(),
        bitvector: BTreeMap::new(),
        algebraic: BTreeMap::new(),
        integer_scope: 0,
        bitvector_scope: 0,
        next_scope_id: 1,
        state_aware: true,
        checked_state_binder: None,
        raw_state_load_seen: false,
        registered_load_stack: BTreeSet::new(),
        registered_load_memo: HashMap::new(),
        pointer_load_stack: BTreeSet::new(),
        pointer_load_memo: HashMap::new(),
        load_interner: None,
        work_units: 0,
    }
}

pub(super) fn machine_fold_key<const ALLOW_LOADS: bool>(
    arguments: [MachineOperandView<'_>; 4],
    accumulator: Variable,
    item: Variable,
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaBitvectorKey> {
    let [start, end, initial, body] = arguments;
    let start = alpha_machine_key::<ALLOW_LOADS>(start, bindings, next_binder)?;
    let end = alpha_machine_key::<ALLOW_LOADS>(end, bindings, next_binder)?;
    let initial = alpha_machine_key::<ALLOW_LOADS>(initial, bindings, next_binder)?;
    let accumulator_ordinal = *next_binder;
    *next_binder = (*next_binder).checked_add(1)?;
    let item_ordinal = *next_binder;
    *next_binder = (*next_binder).checked_add(1)?;
    let bitvector_scope = bindings.next_scope_id;
    bindings.next_scope_id = bitvector_scope.checked_add(1)?;
    let previous_accumulator = bindings.bitvector.insert(accumulator, accumulator_ordinal);
    let previous_item = bindings.bitvector.insert(item, item_ordinal);
    let previous_scope = bindings.bitvector_scope;
    bindings.bitvector_scope = bitvector_scope;
    let body = alpha_machine_key::<ALLOW_LOADS>(body, bindings, next_binder);
    bindings.bitvector_scope = previous_scope;
    // Restore in reverse order even when the selected body refused a key.
    if let Some(previous) = previous_item {
        bindings.bitvector.insert(item, previous);
    } else {
        bindings.bitvector.remove(&item);
    }
    if let Some(previous) = previous_accumulator {
        bindings.bitvector.insert(accumulator, previous);
    } else {
        bindings.bitvector.remove(&accumulator);
    }
    Some(AlphaBitvectorKey::RangeFold {
        start: Box::new(start),
        end: Box::new(end),
        initial: Box::new(initial),
        body: Box::new(body?),
    })
}

pub(crate) fn integer_key(fold: &KernelFold) -> Option<IntegerFoldAlphaKey> {
    if fold.result_type() != &KernelType::Integer {
        return None;
    }
    let mut bindings = bindings();
    alpha_work_checkpoint(&mut bindings, 1)?;
    let mut builder = RetainedIntegerKey::default();
    let node = builder.fold(fold, &mut bindings, &mut 0)?;
    let root = builder.nodes.len();
    builder.nodes.push(node);
    Some(IntegerFoldAlphaKey {
        key: AlphaIntegerKey {
            nodes: builder.nodes,
            root,
        },
        work_units: bindings.work_units,
    })
}

/// Integer variables, arithmetic and mathematical range binders are unchanged
/// by comparison normalization. Other nodes need the existing normalization
/// before they can supply a fact key.
pub(super) fn unchanged_integer_comparison_key(
    operator: IntegerComparisonOperator,
    [left, right]: &[KernelTerm; 2],
) -> Option<IntegerConditionAlphaKey> {
    let mut bindings = bindings();
    alpha_work_checkpoint(&mut bindings, 1)?;
    alpha_work_checkpoint(&mut bindings, 1)?;
    let mut next_binder = 0;
    let mut operand_key = |operand| {
        RetainedIntegerKey {
            unchanged_in_comparisons: true,
            ..Default::default()
        }
        .into_key(operand, &mut bindings, &mut next_binder)
    };
    let condition =
        AlphaConditionKey::IntegerComparison(operator, operand_key(left)?, operand_key(right)?);
    #[cfg(test)]
    ALPHA_PROPOSITION_KEY_VISITS.with(|visits| visits.set(visits.get() + 1));
    Some(IntegerConditionAlphaKey {
        key: AlphaPropositionKey::Condition(condition, true),
        work_units: bindings.work_units,
    })
}

pub(super) fn integer_operand_key(
    term: &KernelTerm,
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaIntegerKey> {
    RetainedIntegerKey::integer(term, bindings, next_binder)
}

#[derive(Default)]
struct RetainedIntegerKey {
    nodes: Vec<AlphaIntegerNode>,
    retained: HashMap<(u64, u64, u64), usize>,
    native: HashMap<(u64, u64, u64), usize>,
    argument_export: KernelTermExport,
    unchanged_in_comparisons: bool,
}

impl RetainedIntegerKey {
    fn node(
        &mut self,
        term: &KernelTerm,
        bindings: &mut AlphaBindings,
        next_binder: &mut usize,
    ) -> Option<usize> {
        let key = (term.id(), bindings.integer_scope, bindings.bitvector_scope);
        if let Some(index) = self.retained.get(&key) {
            return Some(*index);
        }
        alpha_work_checkpoint(bindings, 1)?;
        use KernelTermNode as Node;
        if self.unchanged_in_comparisons
            && !matches!(
                term.node(),
                Node::IntegerLiteral(_)
                    | Node::Variable(_)
                    | Node::IntegerOperation { .. }
                    | Node::Fold(KernelFold {
                        index: KernelFoldIndex::Integer,
                        ..
                    })
            )
        {
            return None;
        }
        let node = match term.node() {
            Node::IntegerLiteral(value) => {
                alpha_work_checkpoint(bindings, (value.bits() as usize).saturating_add(1))?;
                AlphaIntegerNode::Constant(value.clone())
            }
            Node::Variable(variable) => AlphaIntegerNode::Variable(alpha_variable_key::<false>(
                *variable,
                &bindings.integer,
            )?),
            Node::MachineObservation { format, operand } => {
                let key = if operand.ty() == &KernelType::Program(format.program_type())
                    && operand.is_shared_machine_operand()
                {
                    alpha_machine_key::<false>(
                        MachineOperandView::Shared(operand),
                        bindings,
                        next_binder,
                    )?
                } else {
                    let machine = KernelTermExport::machine(operand).ok()?;
                    alpha_machine_key::<false>(
                        MachineOperandView::Legacy(&machine),
                        bindings,
                        next_binder,
                    )?
                };
                AlphaIntegerNode::Machine(*format, key)
            }
            Node::IntegerOperation {
                operator,
                arguments,
            } => {
                let left = self.node(&arguments[0], bindings, next_binder)?;
                match operator {
                    KernelIntegerOperator::Negate => AlphaIntegerNode::Negate(left),
                    operator => {
                        let operator = match operator {
                            KernelIntegerOperator::Add => IntegerTermBinaryOp::Add,
                            KernelIntegerOperator::Subtract => IntegerTermBinaryOp::Subtract,
                            KernelIntegerOperator::Multiply => IntegerTermBinaryOp::Multiply,
                            KernelIntegerOperator::TruncatingQuotient => {
                                IntegerTermBinaryOp::TruncatingQuotient
                            }
                            KernelIntegerOperator::TruncatingRemainder => {
                                IntegerTermBinaryOp::TruncatingRemainder
                            }
                            KernelIntegerOperator::Negate => unreachable!(),
                        };
                        AlphaIntegerNode::Binary {
                            operator,
                            left,
                            right: self.node(&arguments[1], bindings, next_binder)?,
                        }
                    }
                }
            }
            Node::Fold(fold) => self.fold(fold, bindings, next_binder)?,
            Node::IntegerIf {
                arguments: [condition, yes, no],
            } => AlphaIntegerNode::If {
                condition: Box::new(self.condition(condition, bindings, next_binder)?),
                then_term: self.node(yes, bindings, next_binder)?,
                else_term: self.node(no, bindings, next_binder)?,
            },
            Node::Call { name, arguments } => AlphaIntegerNode::PureFunctionApplication {
                name: name.clone(),
                arguments: self.arguments(arguments, bindings, next_binder)?,
            },
            Node::Legacy(value) => {
                let PureFunctionArgument::Integer(value) = value.value() else {
                    return None;
                };
                let index = alpha_integer_node(
                    value,
                    bindings,
                    &mut self.native,
                    &mut self.nodes,
                    next_binder,
                )?;
                self.retained.insert(key, index);
                return Some(index);
            }
            // The native alpha key refuses algebraic matches too.
            _ => return None,
        };
        let index = self.nodes.len();
        self.nodes.push(node);
        self.retained.insert(key, index);
        Some(index)
    }

    fn fold(
        &mut self,
        fold: &KernelFold,
        bindings: &mut AlphaBindings,
        next_binder: &mut usize,
    ) -> Option<AlphaIntegerNode> {
        let [start, end, initial, body] = &fold.arguments;
        let index = match fold.index {
            KernelFoldIndex::Integer => AlphaIntegerRangeIndex::Integer(
                self.node(start, bindings, next_binder)?,
                self.node(end, bindings, next_binder)?,
            ),
            KernelFoldIndex::Int32 | KernelFoldIndex::UInt64 => {
                if !start.is_shared_machine_operand() || !end.is_shared_machine_operand() {
                    return None;
                }
                // Native Integer folds historically key both machine-index forms
                // through the same retagged endpoint carrier.
                let start = start.with_machine_observation_type(MachineIntegerType::Int32);
                let end = end.with_machine_observation_type(MachineIntegerType::Int32);
                let start = alpha_machine_key::<false>(
                    MachineOperandView::Shared(&start),
                    bindings,
                    next_binder,
                )?;
                let end = alpha_machine_key::<false>(
                    MachineOperandView::Shared(&end),
                    bindings,
                    next_binder,
                )?;
                if fold.index == KernelFoldIndex::Int32 {
                    AlphaIntegerRangeIndex::Int32(start, end)
                } else {
                    AlphaIntegerRangeIndex::UInt64(start, end)
                }
            }
        };
        let initial = self.node(initial, bindings, next_binder)?;
        alpha_integer_fold_node(
            index,
            initial,
            fold.accumulator,
            fold.item,
            bindings,
            next_binder,
            |bindings, next_binder| self.node(body, bindings, next_binder),
        )
    }

    fn integer(
        term: &KernelTerm,
        bindings: &mut AlphaBindings,
        next_binder: &mut usize,
    ) -> Option<AlphaIntegerKey> {
        Self::default().into_key(term, bindings, next_binder)
    }

    fn into_key(
        mut self,
        term: &KernelTerm,
        bindings: &mut AlphaBindings,
        next_binder: &mut usize,
    ) -> Option<AlphaIntegerKey> {
        let root = self.node(term, bindings, next_binder)?;
        Some(AlphaIntegerKey {
            nodes: self.nodes,
            root,
        })
    }

    fn arguments(
        &mut self,
        arguments: &[KernelTerm],
        bindings: &mut AlphaBindings,
        next_binder: &mut usize,
    ) -> Option<Vec<AlphaPureFunctionArgumentKey>> {
        arguments
            .iter()
            .map(|argument| {
                if argument.ty() == &KernelType::Integer {
                    alpha_work_checkpoint(bindings, 1)?;
                    return Some(AlphaPureFunctionArgumentKey::Integer(Self::integer(
                        argument,
                        bindings,
                        next_binder,
                    )?));
                }
                // Mixed arguments still use the existing key for that value family.
                let argument = self.argument_export.argument(argument).ok()?;
                alpha_pure_function_argument_key_with_bindings::<false>(
                    &argument,
                    bindings,
                    next_binder,
                )
            })
            .collect()
    }

    fn condition(
        &mut self,
        condition: &KernelTerm,
        bindings: &mut AlphaBindings,
        next_binder: &mut usize,
    ) -> Option<AlphaConditionKey> {
        use KernelTermNode as Node;
        alpha_work_checkpoint(bindings, 1)?;
        Some(match condition.node() {
            Node::IntegerCompare {
                operator,
                arguments: [left, right],
            } => AlphaConditionKey::IntegerComparison(
                *operator,
                Self::integer(left, bindings, next_binder)?,
                Self::integer(right, bindings, next_binder)?,
            ),
            Node::BoolEqual {
                arguments: [left, right],
            } => AlphaConditionKey::BoolEqual(
                Box::new(self.condition(left, bindings, next_binder)?),
                Box::new(self.condition(right, bindings, next_binder)?),
            ),
            Node::BoolIf {
                arguments: [guard, yes, no],
            } => AlphaConditionKey::BoolIf(
                Box::new(self.condition(guard, bindings, next_binder)?),
                Box::new(self.condition(yes, bindings, next_binder)?),
                Box::new(self.condition(no, bindings, next_binder)?),
            ),
            Node::Call { name, arguments } => AlphaConditionKey::BoolApplication {
                name: name.clone(),
                arguments: self.arguments(arguments, bindings, next_binder)?,
            },
            _ => {
                let condition = KernelTermExport::condition(condition).ok()?;
                return alpha_condition_key_with_bindings::<false>(
                    &condition,
                    bindings,
                    next_binder,
                );
            }
        })
    }
}

fn machine_key(fold: &KernelFold) -> Option<(AlphaBitvectorKey, usize)> {
    if fold.result_type() != &KernelType::Program(ProgramType::Int32) {
        return None;
    }
    let mut bindings = bindings();
    alpha_work_checkpoint(&mut bindings, 1)?;
    let key = machine_fold_key::<false>(
        fold.arguments.each_ref().map(MachineOperandView::Shared),
        fold.accumulator,
        fold.item,
        &mut bindings,
        &mut 0,
    )?;
    Some((key, bindings.work_units))
}

pub(crate) fn alpha_equivalent(left: &KernelFold, right: &KernelFold) -> Option<bool> {
    if left.result_type() != right.result_type() || left.index != right.index {
        return Some(false);
    }
    if left.result_type() == &KernelType::Integer {
        return integer_key(left)?.checked_eq(&integer_key(right)?);
    }
    let (left, left_work) = machine_key(left)?;
    let (right, right_work) = machine_key(right)?;
    if crate::instrumentation::deadline_exceeded_with_work(left_work.saturating_add(right_work)) {
        return None;
    }
    Some(left == right)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{IntegerRangeFoldIndex, KernelTermImport};

    fn machine_fold(accumulator: u64, item: u64, body: MachineTerm) -> MachineTerm {
        MachineTerm::RangeFold {
            start: Box::new(MachineTerm::constant(0)),
            end: Box::new(MachineTerm::constant(9)),
            initial: Box::new(MachineTerm::Variable(Variable(80))),
            accumulator: Variable(accumulator),
            item: Variable(item),
            body: Box::new(body),
        }
    }

    #[test]
    fn common_machine_fold_keys_agree_with_native_binders_and_free_variables() {
        let left = machine_fold(81, 82, MachineTerm::Variable(Variable(81)));
        for right in [
            machine_fold(91, 92, MachineTerm::Variable(Variable(91))),
            machine_fold(91, 92, MachineTerm::Variable(Variable(81))),
            machine_fold(91, 92, MachineTerm::Variable(Variable(92))),
        ] {
            let expected = bitvector_folds_alpha_equivalent(&left, &right);
            assert!(expected.is_some());
            let left = KernelFold::import_machine(&mut KernelTermImport::default(), &left).unwrap();
            let right =
                KernelFold::import_machine(&mut KernelTermImport::default(), &right).unwrap();
            assert_eq!(alpha_equivalent(&left, &right), expected);
            assert_ne!(left, right);
        }
        let a = KernelFold::import_machine(&mut KernelTermImport::default(), &left).unwrap();
        assert_eq!(alpha_equivalent(&a, &a), Some(true));
    }

    #[test]
    fn common_integer_fold_keys_preserve_range_kind_and_outer_scope() {
        let native = |acc, item| IntegerTerm::RangeFold {
            index: IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::constant_i64(9).into(),
            },
            initial: IntegerTerm::Variable(Variable(81)).into(),
            accumulator: Variable(acc),
            item: Variable(item),
            body: IntegerTerm::Variable(Variable(acc)).into(),
        };
        let left = native(81, 82);
        let right = native(91, 92);
        let a = KernelFold::import_integer(&mut KernelTermImport::default(), &left).unwrap();
        let b = KernelFold::import_integer(&mut KernelTermImport::default(), &right).unwrap();
        assert_eq!(alpha_equivalent(&a, &b), Some(true));
        assert_eq!(
            integer_key(&a).unwrap(),
            integer_fold_alpha_key(&left.into()).unwrap()
        );
        let mut changed = b.clone();
        changed.arguments[2] = KernelTerm::variable(KernelType::Integer, Variable(91));
        assert_eq!(alpha_equivalent(&a, &changed), Some(false));
        let machine_bound = |format| {
            KernelTerm::retained_machine_operand(
                format,
                MachineOperandView::Legacy(&MachineTerm::Variable(Variable(80))),
            )
        };
        let fold = |kind, format| {
            KernelFold::new(
                kind,
                Variable(81),
                Variable(82),
                [
                    machine_bound(format),
                    machine_bound(format),
                    a.arguments[2].clone(),
                    a.arguments[3].clone(),
                ],
            )
            .unwrap()
        };
        let signed = fold(KernelFoldIndex::Int32, MachineIntegerType::Int32);
        let unsigned = fold(KernelFoldIndex::UInt64, MachineIntegerType::UInt64);
        assert_eq!(alpha_equivalent(&signed, &unsigned), Some(false));
        assert_eq!(alpha_equivalent(&signed, &signed), Some(true));
        for fold in [signed, unsigned] {
            let reference = fold
                .integer_compatibility(&mut KernelTermExport::default())
                .unwrap();
            assert_eq!(
                integer_key(&fold),
                integer_fold_alpha_key(&reference.into())
            );
        }
    }

    #[test]
    fn retained_integer_folds_match_native_keys_for_nested_scopes_and_calls() {
        let _session = crate::kernel::VerificationSession::enter();
        let fold = |accumulator: u64, free: Variable| {
            let acc = Variable(accumulator);
            let item = Variable(accumulator + 1);
            let zero = KernelTerm::integer_literal(0.into());
            let acc_value = KernelTerm::variable(KernelType::Integer, acc);
            let free_value = KernelTerm::variable(KernelType::Integer, free);
            let index = KernelTerm::variable(KernelType::Integer, item);
            let call = KernelTerm::checked_call(
                KernelType::Integer,
                "selected".to_owned(),
                vec![acc_value.clone(), index.clone()],
            );
            let guard = KernelTerm::integer_comparison(
                IntegerComparisonOperator::LessEqual,
                [call.clone(), free_value.clone()],
            )
            .unwrap();
            let inner = KernelFold::new(
                KernelFoldIndex::Integer,
                acc,
                item,
                [
                    zero.clone(),
                    free_value.clone(),
                    index,
                    KernelTerm::integer_if_raw([guard, call, acc_value]),
                ],
            )
            .unwrap();
            KernelFold::new(
                KernelFoldIndex::Integer,
                acc,
                item,
                [zero.clone(), free_value, zero, inner.into_term()],
            )
            .unwrap()
        };
        let free = Variable(100);
        let folds = [fold(101, free), fold(201, free), fold(301, Variable(401))];
        for fold in &folds {
            let native = fold
                .integer_compatibility(&mut KernelTermExport::default())
                .unwrap();
            assert_eq!(integer_key(fold), integer_fold_alpha_key(&native.into()));
        }
        assert_eq!(alpha_equivalent(&folds[0], &folds[1]), Some(true));
        assert_eq!(alpha_equivalent(&folds[0], &folds[2]), Some(false));
    }

    #[test]
    fn common_fold_keys_preserve_state_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = crate::kernel::SymbolicMemory::new();
        let pointer = Address::symbolic(Variable(101));
        let later = memory.clone().store(
            pointer.clone(),
            ProgramValue::Int32(MachineTerm::constant(1)),
        );
        let fold = |memory: &crate::kernel::SymbolicMemory| {
            let native = machine_fold(
                81,
                82,
                MachineTerm::MemoryLoad(
                    crate::kernel::ProgramPoint::at(&(crate::kernel::intern_memory_ref(memory))),
                    Box::new(pointer.clone()),
                    LoadKind::Int32,
                ),
            );
            KernelFold::import_machine(&mut KernelTermImport::default(), &native).unwrap()
        };
        let a = fold(&memory);
        let b = fold(&later);
        assert_eq!(alpha_equivalent(&a, &a), Some(true));
        assert_eq!(alpha_equivalent(&a, &b), Some(false));

        let to_integer = |machine: KernelFold| {
            let zero = KernelTerm::integer_literal(0.into());
            KernelFold::new(
                KernelFoldIndex::Int32,
                machine.accumulator,
                machine.item,
                [
                    machine.arguments[3].clone(),
                    machine.arguments[1].clone(),
                    zero.clone(),
                    zero,
                ],
            )
            .unwrap()
        };
        let a = to_integer(a);
        let b = to_integer(b);
        assert_eq!(alpha_equivalent(&a, &b), Some(false));
        let reference = a
            .integer_compatibility(&mut KernelTermExport::default())
            .unwrap();
        assert_eq!(integer_key(&a), integer_fold_alpha_key(&reference.into()));
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/fact_keys/fold_keys.rs");
}
