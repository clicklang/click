//! Descent context follows native transitions into ordinary outcome completion.
use super::*;

/// Native transition provenance. This does not discharge its ordinary premises;
/// the outcome proof must still complete before the root retires descent.
#[derive(Clone, Debug)]
pub(crate) struct DescentStep {
    anchor: Arc<RecursionAnchor>,
}
impl PartialEq for DescentStep {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.anchor, &other.anchor)
    }
}
impl Eq for DescentStep {}

impl DescentStep {
    pub(in crate::kernel) fn under(environment: &ExecutionEnvironment) -> Option<Self> {
        environment
            .recursion_anchor_handle()
            .map(|anchor| Self { anchor })
    }
}

/// Opened before a body starts. Each checked statement uses this same native
/// context, so applying a recursive call or summary owes its descent here.
#[derive(Clone, Debug)]
pub(in crate::kernel) struct OpenedDescent {
    anchor: Arc<RecursionAnchor>,
}
impl OpenedDescent {
    pub fn open(
        function: &ProgramFunction,
        environment: &ExecutionEnvironment,
    ) -> Result<Option<Self>, String> {
        let opened = Self::inherit(function, environment)?;
        if opened.as_ref().is_some_and(|opened| {
            !opened
                .anchor
                .ranks(function.name(), function.contract_interface())
        }) {
            return Err(format!(
                "opening `{}` requires its declared recursion anchor",
                function.name()
            ));
        }
        Ok(opened)
    }

    /// A fragment of this function inherits the context validated at entry.
    /// Its constructor consumes that native context, not another measure
    /// declaration to recompare at every loop-preservation opening.
    pub fn inherit(
        function: &ProgramFunction,
        environment: &ExecutionEnvironment,
    ) -> Result<Option<Self>, String> {
        charge_termination_work(1);
        if !function.contract_interface().has_call_ranked_recursion() {
            return Ok(None);
        }
        let anchor = environment
            .recursion_anchor_handle()
            .filter(|anchor| anchor.function() == function.name())
            .ok_or_else(|| {
                format!(
                    "opening `{}` requires its declared recursion anchor",
                    function.name()
                )
            })?;
        Ok(Some(Self { anchor }))
    }
    pub fn accept(&self, step: Option<&DescentStep>) -> Result<(), &'static str> {
        charge_termination_work(1);
        if step.is_some_and(|step| Arc::ptr_eq(&self.anchor, &step.anchor)) {
            Ok(())
        } else {
            Err("statement transition belongs to another recursion descent context")
        }
    }
    pub fn accept_environment(
        &self,
        environment: &ExecutionEnvironment,
    ) -> Result<(), &'static str> {
        self.accept(DescentStep::under(environment).as_ref())
    }
}

/// The ordinary root's descent cells have completed. Its private constructor
/// is used only when the root packages its already completed proof.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) struct DescentCompletion(());
impl DescentCompletion {
    pub(in crate::kernel) fn from_completed_root() -> Arc<Self> {
        Arc::new(Self(()))
    }
}

#[cfg(test)]
mod tests {
    use super::super::loop_evidence::tests::{completed_body, ranked_body};
    use super::*;

    fn function() -> ProgramFunction {
        ProgramFunction::new(ProgramType::Void, "ranked", vec![], ProgramStatement::Skip)
            .with_recursion_measure(vec![RankingComponent::ProgramExpression(
                crate::kernel::program_expression::int32_literal(0),
            )])
            .with_recursion_peers(vec!["peer".into()])
    }
    fn environment(function: &ProgramFunction) -> ExecutionEnvironment {
        crate::kernel::program_execution_environment_with_recursion_anchor(
            ExecutionEnvironment::new(),
            function,
            &ExecutionState::new(),
            &[],
        )
        .unwrap()
    }
    #[test]
    fn opening_requires_the_declared_descent_context() {
        assert!(OpenedDescent::open(&function(), &ExecutionEnvironment::new()).is_err());
        let function = function();
        let environment = environment(&function);
        let opened = OpenedDescent::open(&function, &environment)
            .unwrap()
            .unwrap();
        assert!(
            opened
                .accept(DescentStep::under(&environment).as_ref())
                .is_ok()
        );
        assert!(opened.accept(None).is_err());
        assert!(
            opened
                .accept(DescentStep::under(&self::environment(&function)).as_ref())
                .is_err()
        );
    }
    #[test]
    fn only_completed_outcomes_retire_root_owned_descent() {
        let (root, execution) = ranked_body(0);
        let attempt = root.begin_attempt();
        completed_body(attempt.root(), execution.clone(), vec![]).publish(false);
        drop(attempt);
        assert!(root.finish().is_err());
        let attempt = root.begin_attempt();
        completed_body(attempt.root(), execution, vec![]).publish(false);
        attempt.commit();
        assert!(
            root.finish()
                .unwrap()
                .into_rule()
                .unwrap()
                .descent_completion
                .is_some()
        );
    }
    #[test]
    fn a_summary_must_answer_for_recursive_peers() {
        let statement = crate::kernel::program_while(
            crate::kernel::program_expression::int32_literal(0),
            vec![],
            crate::kernel::program_call("peer", vec![]),
        );
        let function = function()
            .with_source_body(statement.clone())
            .with_body(statement.clone());
        let anchored = environment(&function);
        for (producing, expected) in [
            (ExecutionEnvironment::new(), false),
            (anchored.clone(), true),
        ] {
            let (_, rule) = crate::kernel::api::prove_symbolic_execution_statement_verification_paths_with_environment_and_loop_rule_using_budget(
                ExecutionState::new(), function.open_loop_proof(0, statement.clone()).unwrap(),
                PureFactContext::new(), producing, ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
                &mut ExecutionBudget::default(),
            );
            let environment = anchored.clone().with_verified_loop_rules([rule.unwrap()]);
            assert_eq!(
                environment.verified_loop_rules_answer_for_recursion(),
                expected
            );
        }
    }
    mod scaling_tests {
        use super::*;
        include!("../../scaling_tests/kernel/termination/descent_completion.rs");
    }
}
