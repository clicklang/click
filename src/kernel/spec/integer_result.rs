//! Integer evaluator results retain one common root. Native readers cross an
//! explicit compatibility boundary; path facts and obligations stay separate.
use super::*;

#[derive(Clone, Debug)]
pub(in crate::kernel) struct IntegerResult(KernelTerm);

impl From<IntegerTerm> for IntegerResult {
    fn from(value: IntegerTerm) -> Self {
        Self(KernelTermImport::default().integer(&value.into()))
    }
}
impl From<SharedIntegerTerm> for IntegerResult {
    fn from(value: SharedIntegerTerm) -> Self {
        Self(KernelTermImport::default().integer(&value))
    }
}
impl IntegerResult {
    pub(super) fn from_kernel(root: KernelTerm) -> Self {
        Self(root)
    }
    pub(super) fn operation(operator: KernelIntegerOperator, arguments: Vec<Self>) -> Self {
        Self(
            KernelTerm::integer_operation(
                operator,
                arguments.into_iter().map(Self::into_kernel).collect(),
            )
            .expect("typed Integer result operands"),
        )
    }
    pub(super) fn conditional(
        condition: OldConditionTerm,
        then_value: Self,
        else_value: Self,
    ) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        match condition {
            OldConditionTerm::Constant(true) => return then_value,
            OldConditionTerm::Constant(false) => return else_value,
            _ => {}
        }
        if then_value.same_native_syntax(&else_value) {
            return then_value;
        }
        Self(KernelTerm::integer_if_raw([
            KernelTermImport::default().condition(&condition),
            then_value.0,
            else_value.0,
        ]))
    }

    fn same_native_syntax(&self, other: &Self) -> bool {
        self.0.integer_native_syntax_equal(&other.0)
    }

    pub(super) fn range_fold(
        index: IntegerFoldIndexResult,
        initial: Self,
        accumulator: Variable,
        item: Variable,
        body: Self,
    ) -> Self {
        Self(
            KernelFold::new(
                index.kind,
                accumulator,
                item,
                [
                    index.bounds[0].clone(),
                    index.bounds[1].clone(),
                    initial.into_kernel(),
                    body.into_kernel(),
                ],
            )
            .expect("Integer fold result types")
            .into_term(),
        )
    }

    pub(super) fn bits(&self) -> usize {
        self.as_const()
            .and_then(|value| usize::try_from(value.bits()).ok())
            .unwrap_or(1)
            .saturating_add(1)
    }
    pub(super) fn into_kernel(self) -> KernelTerm {
        self.0
    }
    pub(super) fn old_form(&self) -> SharedIntegerTerm {
        KernelTermExport::default()
            .integer(&self.0)
            .expect("Integer result compatibility boundary")
    }
    pub(in crate::kernel) fn into_native_compat(self) -> IntegerTerm {
        self.old_form().as_ref().clone()
    }
    pub(super) fn as_const(&self) -> Option<&num_bigint::BigInt> {
        match self.0.node() {
            KernelTermNode::IntegerLiteral(value) => Some(value),
            _ => None,
        }
    }
}
impl KernelTerm {
    // IntegerTerm's equality is structural, with its existing observation and
    // application identities at scalar leaves. Compare common connectives
    // directly; never export a whole arithmetic/conditional prefix merely to
    // decide the equal-arm construction rule.
    pub(in crate::kernel) fn integer_native_syntax_equal(&self, other: &Self) -> bool {
        let mut pending = vec![(self, other)];
        let mut seen = std::collections::HashSet::new();
        while let Some((left, right)) = pending.pop() {
            if left == right || !seen.insert((left.id(), right.id())) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            if left.is_mathematical_integer() && right.is_mathematical_integer() {
                // Their exact syntax is the common interner key.
                return false;
            }
            match (left.node(), right.node()) {
                (
                    KernelTermNode::IntegerOperation {
                        operator: a,
                        arguments: aa,
                    },
                    KernelTermNode::IntegerOperation {
                        operator: b,
                        arguments: ba,
                    },
                ) if a == b => {
                    pending.extend(aa.iter().zip(ba));
                }
                (
                    KernelTermNode::IntegerIf { arguments: a },
                    KernelTermNode::IntegerIf { arguments: b },
                ) => {
                    if a[0].condition_storage_key() != b[0].condition_storage_key() {
                        return false;
                    }
                    pending.extend(a[1..].iter().zip(&b[1..]));
                }
                // These leaves retain their separate compatibility contracts.
                // The machine case reconstructs only an observation handle;
                // call/fold/match payload migration remains separately scoped.
                (
                    KernelTermNode::MachineObservation { .. },
                    KernelTermNode::MachineObservation { .. },
                )
                | (KernelTermNode::Call { .. }, KernelTermNode::Call { .. })
                | (KernelTermNode::Fold(_), KernelTermNode::Fold(_))
                | (KernelTermNode::Match(_), KernelTermNode::Match(_)) => {
                    let mut export = KernelTermExport::default();
                    if export.integer(left).expect("Integer equality leaf")
                        != export.integer(right).expect("Integer equality leaf")
                    {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        true
    }
}

impl PartialEq for IntegerResult {
    fn eq(&self, other: &Self) -> bool {
        self.same_native_syntax(other)
    }
}
impl Eq for IntegerResult {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::VerificationSession;

    #[test]
    fn integer_result_holds_the_same_root_as_its_source() {
        let _session = VerificationSession::enter();
        let observation = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            OldMachineTerm::Variable(Variable(1009701)),
        ));
        let expected = IntegerTerm::Add(observation.into(), IntegerTerm::constant_i64(7).into());
        let source: SharedIntegerTerm = expected.clone().into();
        let weak = source.downgrade();
        let value = IntegerResult::from(source.clone());
        drop(source);
        let root = value.clone().into_kernel();
        assert_eq!(weak.upgrade().as_ref(), Some(&root));
        assert!(matches!(
            root.node(),
            KernelTermNode::IntegerOperation {
                operator: KernelIntegerOperator::Add,
                ..
            }
        ));
        assert!(!root.has_cached_native_argument());
        let negated = IntegerResult::operation(KernelIntegerOperator::Negate, vec![value.clone()]);
        assert_eq!(negated.into_kernel().children(), vec![root.clone()]);
        assert_eq!(value.into_native_compat(), expected);
    }

    #[test]
    fn integer_evaluation_paths_retain_common_arithmetic_results() {
        let _session = VerificationSession::enter();
        let expression = SpecIntegerExpression::Add(
            Box::new(SpecIntegerExpression::Term(IntegerTerm::var(Variable(
                1009702,
            )))),
            Box::new(SpecIntegerExpression::Term(IntegerTerm::constant_i64(3))),
        );
        let paths = evaluate_spec_integer_expression_paths_in(
            SpecScope::unbound(&ExecutionState::new(), None),
            &expression,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one arithmetic path")
        };
        let root = path.value.clone().into_kernel();
        assert_eq!(root.ty(), &KernelType::Integer);
        assert!(matches!(
            root.node(),
            KernelTermNode::IntegerOperation {
                operator: KernelIntegerOperator::Add,
                ..
            }
        ));
        assert!(path.facts.is_empty());
        assert!(path.obligations.is_empty());
        assert!(!root.has_cached_native_argument());
    }
}

#[cfg(test)]
mod conditional_contract_tests {
    use super::*;
    use crate::kernel::VerificationSession;

    #[test]
    fn integer_common_conditionals_keep_native_equal_arm_and_payload_rules() {
        let _session = VerificationSession::enter();
        let ProgramValue::Pointer(pointer) =
            crate::kernel::symbolic_call_result(ProgramType::Int32Pointer, Variable(1009890))
        else {
            unreachable!("typed symbolic pointer")
        };
        let call = |constant: bool| {
            IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                "integer_conditional_pointer".into(),
                vec![PureFunctionArgument::Value(ProgramValue::Pointer(
                    pointer
                        .clone()
                        .with_declared_object_class(constant.then_some(
                            crate::kernel::effective_type::CAccessClass::Scalar(
                                crate::kernel::effective_type::CScalarClass::Int,
                            ),
                        )),
                ))],
            ))
        };
        let calls = [call(false), call(true)];
        assert_eq!(
            calls[0], calls[1],
            "native application identity ignores the pointer's declared class"
        );
        let common_calls = calls.clone().map(IntegerResult::from);
        assert_ne!(
            common_calls[0].0, common_calls[1].0,
            "producer payloads remain distinct"
        );
        let var = IntegerTerm::var(Variable(1009891));
        let values = [
            IntegerTerm::constant_i64(0),
            var.clone(),
            IntegerTerm::Add(var.clone().into(), IntegerTerm::constant_i64(1).into()),
            IntegerTerm::Negate(var.into()),
            calls[0].clone(),
            calls[1].clone(),
        ];
        let retained: Vec<_> = values.iter().cloned().map(IntegerResult::from).collect();
        for condition in [
            OldConditionTerm::Constant(true),
            OldConditionTerm::Constant(false),
            OldConditionTerm::Variable(Variable(1009892)),
        ] {
            for (i, left) in values.iter().enumerate() {
                for (j, right) in values.iter().enumerate() {
                    assert_eq!(
                        retained[i] == retained[j],
                        left == right,
                        "result equality {i}/{j}"
                    );
                    let expected =
                        IntegerTerm::if_then_else(condition.clone(), left.clone(), right.clone());
                    let result = IntegerResult::conditional(
                        condition.clone(),
                        retained[i].clone(),
                        retained[j].clone(),
                    );
                    assert_eq!(result.clone().into_native_compat(), expected, "{i}/{j}");
                    if !matches!(condition, OldConditionTerm::Constant(false)) && left == right {
                        assert_eq!(
                            result.0, retained[i].0,
                            "equal arms retain the left producer"
                        );
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/spec/integer_result.rs");
}
