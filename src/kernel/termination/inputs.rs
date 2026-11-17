//! Explicit adapters for completed ordinary bodies and independent analyses.
use super::*;
use crate::kernel::ContractBodyProof;

/// Produced only while packaging a completed whole-contract root. Its loop
/// namespace and descent authority do not have optional legacy substitutes.
#[derive(Clone, Debug)]
pub(in crate::kernel) struct CompletedBodyTermination {
    pub(super) exits: Arc<loop_evidence::ConcreteLoopExits>,
    _descent: Arc<descent_completion::DescentCompletion>,
}

impl CompletedBodyTermination {
    pub(in crate::kernel) fn from_completed_root(
        exits: Arc<loop_evidence::ConcreteLoopExits>,
    ) -> Self {
        Self {
            exits,
            _descent: descent_completion::DescentCompletion::from_completed_root(),
        }
    }
}

#[derive(Clone, Debug)]
pub(super) enum LocalTerminationInput {
    Completed(CompletedBodyTermination),
    Independent,
}

/// Inputs with no enclosing ordinary body owner. Only this adapter prepares
/// legacy source-loop coverage; completed bodies never pass through it.
pub(crate) struct IndependentTerminationInputs<'a> {
    pub rules: &'a [VerifiedFunctionRule],
    pub bodies: &'a [&'a ProgramFunction],
}

pub(super) struct TerminationBodyInputs {
    pub rules: Vec<VerifiedFunctionRule>,
    completed: BTreeMap<String, CompletedBodyTermination>,
}

impl TerminationBodyInputs {
    pub fn completed(
        bodies: &[Arc<ContractBodyProof>],
        independent: &[VerifiedFunctionRule],
        summaries: &BTreeMap<String, Vec<VerifiedLoopRule>>,
    ) -> Self {
        let mut completed = BTreeMap::new();
        let mut rules = BTreeMap::new();
        for body in bodies {
            charge_termination_work(1);
            let rule = body.termination_rule();
            let name = rule.function.name().to_string();
            completed.insert(name.clone(), body.termination_input().clone());
            rules.insert(name, rule.clone());
        }
        let independent = independent
            .iter()
            .filter(|rule| {
                charge_termination_work(1);
                !completed.contains_key(rule.function.name())
            })
            .cloned()
            .collect::<Vec<_>>();
        for rule in prepare_independent_loop_exits(&independent, summaries) {
            rules.insert(rule.function.name().to_string(), rule);
        }
        Self {
            rules: rules.into_values().collect(),
            completed,
        }
    }

    pub fn local(&self, name: &str) -> LocalTerminationInput {
        charge_termination_work(1);
        match self.completed.get(name) {
            Some(completion) => LocalTerminationInput::Completed(completion.clone()),
            None => LocalTerminationInput::Independent,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::termination::loop_evidence::tests::{completed_body, ranked_body};

    fn completed() -> Arc<ContractBodyProof> {
        let (root, execution) = ranked_body(0);
        let attempt = root.begin_attempt();
        completed_body(attempt.root(), execution, vec![]).publish(false);
        attempt.commit();
        root.finish().unwrap()
    }

    #[test]
    fn completed_inputs_cannot_fall_back_when_legacy_rule_fields_are_absent() {
        let body = completed();
        let mut inputs = TerminationBodyInputs::completed(&[body], &[], &BTreeMap::new());
        let rule = &mut inputs.rules[0];
        rule.descent_completion = None;
        rule.concrete_loop_exits = None;
        rule.function.source_body = crate::kernel::program_while(
            crate::kernel::program_expression::int32_literal(1),
            vec![],
            crate::kernel::program_call("concrete_body", vec![]),
        );
        rule.checked_callees = Some(Arc::new(BTreeSet::from(["concrete_body".into()])));
        let plans = [program_function_termination_plan(
            "concrete_body",
            Some(FunctionTerminationMeasure::Expression("0".into())),
            BTreeMap::new(),
        )];
        let goals = super::super::obligations::TerminationObligations::generate_from_inputs(
            &inputs,
            &plans,
            &BTreeMap::new(),
            &[],
            &program_termination_height_plan(&inputs.rules, &[]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
            false,
            None,
        )
        .unwrap();
        assert!(matches!(
            goals.function_goals["concrete_body"].input,
            LocalTerminationInput::Completed(_)
        ));
        assert!(
            goals
                .prove_local_descent(&"concrete_body".into())
                .unwrap()
                .is_none()
        );
        assert_eq!(goals.function_goals["concrete_body"].loop_indices, [0]);
    }

    #[test]
    fn an_independent_shadow_cannot_downgrade_a_completed_body() {
        let body = completed();
        let mut shadow = body.termination_rule().clone();
        shadow.concrete_loop_exits = None;
        shadow.descent_completion = None;
        shadow.function.source_body = crate::kernel::program_while(
            crate::kernel::program_expression::int32_literal(1),
            vec![],
            ProgramStatement::Skip,
        );
        let inputs = TerminationBodyInputs::completed(
            std::slice::from_ref(&body),
            &[shadow],
            &BTreeMap::new(),
        );
        assert!(matches!(
            inputs.local("concrete_body"),
            LocalTerminationInput::Completed(_)
        ));
        assert_eq!(
            inputs.rules[0].function.source_body,
            body.termination_rule().function.source_body
        );
        let independent = TerminationBodyInputs::completed(&[], &inputs.rules, &BTreeMap::new());
        assert!(matches!(
            independent.local("concrete_body"),
            LocalTerminationInput::Independent
        ));
    }

    mod scaling_tests {
        use super::*;
        include!("../../scaling_tests/kernel/termination/inputs.rs");
    }
}
