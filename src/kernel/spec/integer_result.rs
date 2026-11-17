//! Integer evaluator results retain one common root. Native readers cross an
//! explicit compatibility boundary; path facts and obligations stay separate.
use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
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
    pub(super) fn operation(operator: KernelIntegerOperator, arguments: Vec<Self>) -> Self {
        Self(
            KernelTerm::integer_operation(
                operator,
                arguments.into_iter().map(Self::into_kernel).collect(),
            )
            .expect("typed Integer result operands"),
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
    pub(super) fn native_compat(&self) -> SharedIntegerTerm {
        KernelTermExport::default()
            .integer(&self.0)
            .expect("Integer result compatibility boundary")
    }
    pub(in crate::kernel) fn into_native_compat(self) -> IntegerTerm {
        self.native_compat().as_ref().clone()
    }
    pub(super) fn as_const(&self) -> Option<&num_bigint::BigInt> {
        match self.0.node() {
            KernelTermNode::IntegerLiteral(value) => Some(value),
            _ => None,
        }
    }
}
impl From<IntegerResult> for SharedIntegerTerm {
    fn from(value: IntegerResult) -> Self {
        value.native_compat()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::VerificationSession;

    #[test]
    fn integer_result_releases_native_source_and_keeps_its_common_children() {
        let _session = VerificationSession::enter();
        let source: SharedIntegerTerm = IntegerTerm::Add(
            IntegerTerm::var(Variable(1009701)).into(),
            IntegerTerm::constant_i64(7).into(),
        )
        .into();
        let weak = source.downgrade();
        let expected = source.as_ref().clone();
        let value = IntegerResult::from(source.clone());
        drop(source);
        assert!(weak.upgrade().is_none());
        let root = value.clone().into_kernel();
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
mod scaling_tests {
    include!("../../scaling_tests/kernel/spec/integer_result.rs");
}
