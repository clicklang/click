//! Evaluated fold endpoints retain typed common roots. Native fold indices
//! remain explicit input/checking descriptors, rather than evaluator storage.
use super::*;

#[derive(Clone, Debug)]
pub(super) struct IntegerFoldIndexResult {
    pub(super) kind: KernelFoldIndex,
    pub(super) bounds: [KernelTerm; 2],
}

impl IntegerFoldIndexResult {
    pub(super) fn item_domain(&self, item: Variable) -> (Sort, Proposition) {
        use crate::kernel::machine_integer::comparison::condition_for_operand_views;
        use crate::kernel::{CompareRelation as R, MachineOperandView as V};
        let [start, end] = &self.bounds;
        match self.kind {
            KernelFoldIndex::Integer => {
                // ConditionTerm is still an explicit native proposition-output
                // boundary (10q); the retained endpoints themselves stay common.
                let mut output = KernelTermExport::default();
                let start = output.integer(start).expect("Integer fold start");
                let end = output.integer(end).expect("Integer fold end");
                let item = IntegerTerm::Variable(item);
                (
                    Sort::Integer,
                    Proposition::And(
                        Box::new(Proposition::ConditionIs(
                            ConditionTerm::integer_greater_equal(
                                item.clone(),
                                start.as_ref().clone(),
                            ),
                            true,
                        )),
                        Box::new(Proposition::ConditionIs(
                            ConditionTerm::integer_less_than(item, end.as_ref().clone()),
                            true,
                        )),
                    ),
                )
            }
            kind => {
                let format = if kind == KernelFoldIndex::Int32 {
                    MachineIntegerType::Int32
                } else {
                    MachineIntegerType::UInt64
                };
                let item = MachineTerm::Variable(item);
                let lower = if kind == KernelFoldIndex::Int32 {
                    condition_for_operand_views(
                        format,
                        R::GreaterEqual,
                        [V::Legacy(&item), V::Shared(start)],
                    )
                } else {
                    condition_for_operand_views(
                        format,
                        R::LessEqual,
                        [V::Shared(start), V::Legacy(&item)],
                    )
                };
                let upper = condition_for_operand_views(
                    format,
                    R::LessThan,
                    [V::Legacy(&item), V::Shared(end)],
                );
                (
                    if kind == KernelFoldIndex::Int32 {
                        Sort::ProgramInt32
                    } else {
                        Sort::ProgramInteger(format)
                    },
                    Proposition::And(
                        Box::new(Proposition::ConditionIs(lower, true)),
                        Box::new(Proposition::ConditionIs(upper, true)),
                    ),
                )
            }
        }
    }

    pub(super) fn is_empty(&self) -> bool {
        let [start, end] = &self.bounds;
        match self.kind {
            KernelFoldIndex::Integer => match (start.node(), end.node()) {
                (KernelTermNode::IntegerLiteral(a), KernelTermNode::IntegerLiteral(b)) => a >= b,
                _ => false,
            },
            KernelFoldIndex::Int32 => match (
                MachineOperandView::Shared(start).word32_constant(),
                MachineOperandView::Shared(end).word32_constant(),
            ) {
                (Some(a), Some(b)) => a as i32 >= b as i32,
                _ => false,
            },
            KernelFoldIndex::UInt64 => match (
                MachineOperandView::Shared(start).uint64_constant(),
                MachineOperandView::Shared(end).uint64_constant(),
            ) {
                (Some(a), Some(b)) => a >= b,
                _ => false,
            },
        }
    }
}

#[cfg(test)]
impl From<IntegerRangeFoldIndex> for IntegerFoldIndexResult {
    fn from(value: IntegerRangeFoldIndex) -> Self {
        let (kind, start, end) =
            KernelFold::integer_index(&mut KernelTermImport::default(), &value);
        Self {
            kind,
            bounds: [start, end],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::VerificationSession;

    #[test]
    fn retained_integer_binding_releases_native_children_and_restores_on_error() {
        let _session = VerificationSession::enter();
        let variable = Variable(1011100);
        let child: SharedIntegerTerm = IntegerTerm::Add(
            IntegerTerm::var(Variable(1011101)).into(),
            IntegerTerm::constant_i64(3).into(),
        )
        .into();
        let weak = child.downgrade();
        let source: SharedIntegerTerm = IntegerTerm::Multiply(child.clone(), child.clone()).into();
        drop(child);
        let root = KernelTermImport::default().integer(&source);
        let fields = [AlgebraicFieldResult::Shared(root.clone())];
        let mut execution_budget = ExecutionBudget::default();
        let mut evaluation = SpecEvaluation::logical(&mut execution_budget);
        let previous = IntegerResult::from(IntegerTerm::constant_i64(11));
        evaluation
            .integer_bindings
            .insert(variable, previous.clone());
        let result =
            evaluation.with_retained_integer_bindings(&[Some(variable)], &fields, |evaluation| {
                drop(source);
                assert!(
                    weak.upgrade().is_none(),
                    "a retained binding must not export native children"
                );
                assert_eq!(
                    evaluation
                        .bound_integer_term(&IntegerTerm::var(variable))?
                        .into_kernel(),
                    root
                );
                evaluation.with_integer_bindings(
                    &[Some(variable)],
                    &[AlgebraicValue::Integer(IntegerTerm::constant_i64(22))],
                    |evaluation| {
                        assert_eq!(
                            evaluation
                                .bound_integer_term(&IntegerTerm::var(variable))?
                                .as_const(),
                            Some(&22.into())
                        );
                        Err::<(), _>(ExecutionLimit::Paths)
                    },
                )
            });
        assert_eq!(result, Err(ExecutionLimit::Paths));
        assert_eq!(
            evaluation
                .bound_integer_term(&IntegerTerm::var(variable))
                .unwrap()
                .into_kernel(),
            previous.into_kernel()
        );
    }

    #[test]
    fn integer_fold_endpoint_handoff_keeps_the_bound_producer_root() {
        let _session = VerificationSession::enter();
        let variable = Variable(1011110);
        let root = KernelTerm::integer_operation(
            KernelIntegerOperator::Add,
            vec![
                KernelTerm::variable(KernelType::Integer, Variable(1011111)),
                KernelTerm::variable(KernelType::Integer, Variable(1011112)),
            ],
        )
        .unwrap();
        let index = SpecIntegerRangeFoldIndex::Integer {
            start: Box::new(SpecIntegerExpression::Term(IntegerTerm::var(variable))),
            end: Box::new(SpecIntegerExpression::Term(IntegerTerm::constant_i64(2))),
        };
        let mut execution_budget = ExecutionBudget::default();
        let mut evaluation = SpecEvaluation::logical(&mut execution_budget);
        evaluation
            .integer_bindings
            .insert(variable, IntegerResult::from_kernel(root.clone()));
        let paths = evaluate_spec_integer_range_fold_indices_in(
            SpecScope::unbound(&ExecutionState::new(), None),
            &index,
            &PureFactContext::new(),
            &mut evaluation,
        )
        .unwrap();
        let [(index, facts, obligations)] = paths.as_slice() else {
            panic!("one index path")
        };
        assert_eq!(index.kind, KernelFoldIndex::Integer);
        assert_eq!(index.bounds[0], root);
        assert!(facts.is_empty());
        assert!(obligations.is_empty());
        let fold = IntegerResult::range_fold(
            index.clone(),
            IntegerTerm::constant_i64(0).into(),
            Variable(1011113),
            Variable(1011114),
            IntegerTerm::var(Variable(1011113)).into(),
        )
        .into_kernel();
        assert_eq!(fold.children()[0], root);
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/spec/integer_fold_index.rs");
}
