//! Bind loop evidence before executing its proof, never at termination consumption.
use super::*;

/// One flat executable-shape stream, with a direct range per source loop.
/// Nested loop bodies share ranges instead of cloning their subtrees.
#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct LoopSourceIndex {
    loops: Vec<std::ops::Range<usize>>,
    shape: Vec<ShapeHead>,
    addressed: BTreeSet<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ShapeHead {
    Sequence(usize),
    If(ProgramExpression),
    Loop {
        condition: ProgramExpression,
        do_while: bool,
        backedge_target: Option<ControlTargetId>,
        natural_exit_target: Option<ControlTargetId>,
    },
    Switch(ProgramExpression, Vec<Option<u32>>),
    Try(String, bool),
    Step(Vec<String>, bool),
    Leaf(ProgramStatement),
}

impl ShapeHead {
    fn of(statement: &ProgramStatement) -> Self {
        charge_termination_work(1);
        match statement {
            ProgramStatement::Seq(statements) => Self::Sequence(statements.len()),
            ProgramStatement::If { condition, .. } => Self::If(condition.clone()),
            ProgramStatement::While {
                condition,
                do_while,
                backedge_target,
                natural_exit_target,
                ..
            } => Self::Loop {
                condition: condition.clone(),
                do_while: *do_while,
                backedge_target: *backedge_target,
                natural_exit_target: *natural_exit_target,
            },
            ProgramStatement::Switch { expression, cases } => Self::Switch(
                expression.clone(),
                cases.iter().map(|case| case.value).collect(),
            ),
            ProgramStatement::TryCatchInt32 {
                binding,
                cleanup_unwind,
                ..
            } => Self::Try(binding.clone(), *cleanup_unwind),
            ProgramStatement::ForStep {
                exited_locals,
                continue_after,
                ..
            } => Self::Step(exited_locals.clone(), *continue_after),
            _ => Self::Leaf(statement.clone()),
        }
    }
}

/// Visit only immediate children; heads above exclude those subtrees.
fn children_all(
    statement: &ProgramStatement,
    mut visit: impl FnMut(&ProgramStatement) -> bool,
) -> bool {
    match statement {
        ProgramStatement::While { body, .. } => visit(body),
        ProgramStatement::Seq(statements) => statements.iter().all(|child| visit(child)),
        ProgramStatement::If {
            then_branch,
            else_branch,
            ..
        } => visit(then_branch) && visit(else_branch),
        ProgramStatement::Switch { cases, .. } => cases.iter().all(|case| visit(&case.body)),
        ProgramStatement::TryCatchInt32 {
            try_body, handler, ..
        } => visit(try_body) && visit(handler),
        ProgramStatement::ForStep { step, .. } => visit(step),
        ProgramStatement::Skip
        | ProgramStatement::EndScalarReference(_)
        | ProgramStatement::ScalarReferenceScope(_)
        | ProgramStatement::EndAutomaticLifetimes { .. }
        | ProgramStatement::Break
        | ProgramStatement::Continue
        | ProgramStatement::Goto { .. }
        | ProgramStatement::Declare { .. }
        | ProgramStatement::DeclareAggregate { .. }
        | ProgramStatement::Assign { .. }
        | ProgramStatement::CallConstruct { .. }
        | ProgramStatement::Call { .. }
        | ProgramStatement::CallResult { .. }
        | ProgramStatement::HeapAllocate { .. }
        | ProgramStatement::HeapFree { .. }
        | ProgramStatement::Assert { .. }
        | ProgramStatement::StepValue { .. }
        | ProgramStatement::LoopTest { .. }
        | ProgramStatement::Throw(_)
        | ProgramStatement::Return(_)
        | ProgramStatement::Store { .. }
        | ProgramStatement::TypedStore { .. }
        | ProgramStatement::CopyAggregate { .. }
        | ProgramStatement::InitializeScalarArray { .. }
        | ProgramStatement::Update { .. } => true,
    }
}

impl LoopSourceIndex {
    fn new(function: &ProgramFunction) -> Self {
        let natural = function.natural_loop_source;
        let body = if natural.is_none() && contains_natural_control_loop(function.body()) {
            function.body()
        } else {
            function.source_body()
        };
        let mut index = Self {
            addressed: address_taken_locals(body),
            ..Self::default()
        };
        if let Some((target, exit)) = natural {
            index.loops.push(0..0);
            index.shape.push(ShapeHead::Loop {
                condition: crate::kernel::program_expression::int32_literal(1),
                do_while: false,
                backedge_target: Some(target),
                natural_exit_target: exit,
            });
        }
        index.collect(body);
        if natural.is_some() {
            index.loops[0].end = index.shape.len();
        }
        index
    }
    fn collect(&mut self, statement: &ProgramStatement) {
        let start = self.shape.len();
        let loop_index = if matches!(statement, ProgramStatement::While { .. }) {
            let index = self.loops.len();
            self.loops.push(start..start);
            Some(index)
        } else {
            None
        };
        self.shape.push(ShapeHead::of(statement));
        children_all(statement, |child| {
            self.collect(child);
            true
        });
        if let Some(index) = loop_index {
            self.loops[index].end = self.shape.len();
        }
    }
    fn matches(statement: &ProgramStatement, remaining: &mut &[ShapeHead]) -> bool {
        let Some((head, rest)) = remaining.split_first() else {
            return false;
        };
        if head != &ShapeHead::of(statement) {
            return false;
        }
        *remaining = rest;
        children_all(statement, |child| Self::matches(child, remaining))
    }
}

/// The constructor retains both the selected source identity and the exact
/// annotated statement to execute. There is no API to retag a completed rule.
#[derive(Clone, Debug)]
pub(crate) struct StatementProofInput {
    pub(in crate::kernel) statement: ProgramStatement,
    pub(in crate::kernel) loop_evidence: Option<LoopEvidence>,
}
impl StatementProofInput {
    pub(crate) fn statement(&self) -> &ProgramStatement {
        &self.statement
    }
}
impl From<ProgramStatement> for StatementProofInput {
    fn from(statement: ProgramStatement) -> Self {
        Self {
            statement,
            loop_evidence: None,
        }
    }
}
impl From<&ProgramStatement> for StatementProofInput {
    fn from(statement: &ProgramStatement) -> Self {
        statement.clone().into()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) struct LoopEvidence {
    pub index: usize,
    pub measure: Option<LoopTerminationMeasure>,
}

impl ProgramFunction {
    /// Establish the source index once during function proof setup.
    pub(crate) fn prepare_loop_proofs(&self) {
        self.loop_source_index
            .0
            .get_or_init(|| LoopSourceIndex::new(self));
    }
    pub(crate) fn open_loop_proof(
        &self,
        index: usize,
        statement: ProgramStatement,
    ) -> Result<StatementProofInput, TerminationError> {
        let sources = self
            .loop_source_index
            .0
            .get_or_init(|| LoopSourceIndex::new(self));
        let range = sources.loops.get(index).ok_or_else(|| {
            error(format!(
                "loop proof for `{}` refers to nonexistent loop {index}",
                self.name()
            ))
        })?;
        let mut remaining = &sources.shape[range.clone()];
        if !LoopSourceIndex::matches(&statement, &mut remaining) || !remaining.is_empty() {
            return Err(error(format!(
                "loop proof for `{}` does not match loop {index}'s source shape",
                self.name()
            )));
        }
        let ProgramStatement::While {
            ranking_measures,
            structural_measure,
            ..
        } = &statement
        else {
            unreachable!("the source index selects a loop and the shapes agree")
        };
        for component in ranking_measures {
            reject_address_escaped_ranking_component(self.name(), component, &sources.addressed)?;
        }
        let measure = if let Some(binder) = structural_measure {
            Some(LoopTerminationMeasure::Structural(binder.clone()))
        } else if ranking_measures.is_empty() {
            None
        } else {
            Some(LoopTerminationMeasure::Ranking(
                ranking_measures.iter().map(RankingComponent::key).collect(),
            ))
        };
        Ok(StatementProofInput {
            statement,
            loop_evidence: Some(LoopEvidence { index, measure }),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::program_expression::{int32_literal, variable};

    fn loop_statement() -> ProgramStatement {
        crate::kernel::program_while(int32_literal(0), Vec::new(), ProgramStatement::Skip)
    }
    fn function(body: ProgramStatement) -> ProgramFunction {
        ProgramFunction::new(ProgramType::Void, "loop_owner", Vec::new(), body)
    }
    fn prove(input: StatementProofInput) -> VerifiedLoopRule {
        let (execution, rule) = crate::kernel::api::prove_symbolic_execution_statement_verification_paths_with_environment_and_loop_rule_using_budget(
            ExecutionState::new(), input, PureFactContext::new(), ExecutionEnvironment::new(),
            ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS, &mut ExecutionBudget::default(),
        );
        assert!(execution.limit.is_none());
        rule.expect("the false loop has a checked exit")
    }

    #[test]
    fn source_identity_and_shape_are_established_before_execution() {
        let source = loop_statement();
        let function = function(source.clone());
        assert!(
            function
                .open_loop_proof(1, source.clone())
                .unwrap_err()
                .message()
                .contains("nonexistent loop 1")
        );
        let mut different = source.clone();
        let ProgramStatement::While { condition, .. } = &mut different else {
            unreachable!()
        };
        *condition = int32_literal(1);
        assert!(
            function
                .open_loop_proof(0, different)
                .unwrap_err()
                .message()
                .contains("source shape")
        );
        let rule = prove(function.open_loop_proof(0, source).unwrap());
        assert_eq!(
            rule.loop_evidence,
            Some(LoopEvidence {
                index: 0,
                measure: None
            })
        );
        assert_eq!(
            verified_loop_ranking_measures(&[rule]),
            (BTreeMap::new(), BTreeSet::from([0]))
        );
    }

    #[test]
    fn ineligible_measure_is_refused_at_opening_even_on_an_unreachable_loop() {
        let source = loop_statement();
        let body = ProgramStatement::seq(
            Arc::new(crate::kernel::program_call(
                "escape",
                vec![ProgramExpression::AddressOf(Box::new(variable("n")))],
            )),
            Arc::new(source.clone()),
        );
        let function = function(body);
        let mut annotated = source;
        let ProgramStatement::While {
            ranking_measures, ..
        } = &mut annotated
        else {
            unreachable!()
        };
        *ranking_measures = vec![RankingComponent::ProgramExpression(variable("n"))];
        let error = function.open_loop_proof(0, annotated).unwrap_err();
        assert!(error.message().contains("address"), "{}", error.message());
    }

    #[test]
    fn successful_producer_retains_its_own_measure() {
        let source = loop_statement();
        let function = function(source.clone());
        let mut annotated = source.clone();
        let ProgramStatement::While {
            ranking_measures, ..
        } = &mut annotated
        else {
            unreachable!()
        };
        let component = RankingComponent::ProgramExpression(int32_literal(0));
        *ranking_measures = vec![component.clone()];
        let ranked = prove(function.open_loop_proof(0, annotated).unwrap());
        let (measures, unranked) = verified_loop_ranking_measures(std::slice::from_ref(&ranked));
        assert_eq!(
            measures[&0],
            vec![LoopTerminationMeasure::Ranking(vec![component.key()])]
        );
        assert!(unranked.is_empty());
        let unranked = prove(function.open_loop_proof(0, source.clone()).unwrap());
        assert_eq!(
            verified_loop_ranking_measures(&[ranked, unranked]),
            (BTreeMap::new(), BTreeSet::from([0]))
        );
        // An independently executed raw statement has no source-loop authority.
        let raw = prove(source.into());
        assert!(raw.loop_evidence.is_none());
        assert_eq!(
            verified_loop_ranking_measures(&[raw]),
            (BTreeMap::new(), BTreeSet::new())
        );
    }

    #[test]
    fn failed_execution_does_not_publish_opening_authority() {
        let statement =
            crate::kernel::program_while(int32_literal(1), Vec::new(), ProgramStatement::Skip);
        let owner = function(statement.clone());
        let input = owner.open_loop_proof(0, statement).unwrap();
        let (execution, rule) = crate::kernel::api::prove_symbolic_execution_statement_verification_paths_with_environment_and_loop_rule_using_budget(
            ExecutionState::new(), input, PureFactContext::new(), ExecutionEnvironment::new(),
            ExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut ExecutionBudget::default().with_loop_unrolls(0),
        );
        assert_eq!(execution.limit, Some(ExecutionLimit::LoopUnrolls));
        assert!(rule.is_none());
    }

    #[test]
    fn natural_cycle_identity_exists_before_frontier_annotations() {
        let target = ControlTargetId(7);
        let source = ProgramStatement::Goto { target };
        let function = function(source.clone()).with_natural_loop_source(Some((target, None)));
        function.prepare_loop_proofs();
        let statement = crate::kernel::program_while(int32_literal(1), Vec::new(), source)
            .with_backedge_target(target);
        let opening = function.open_loop_proof(0, statement.clone()).unwrap();
        assert_eq!(opening.loop_evidence.unwrap().index, 0);
        let wrong = statement.with_backedge_target(ControlTargetId(8));
        assert!(
            function
                .open_loop_proof(0, wrong)
                .unwrap_err()
                .message()
                .contains("source shape")
        );
    }

    #[test]
    fn changing_source_invalidates_its_derived_index() {
        let source = loop_statement();
        let original = function(source.clone());
        original.prepare_loop_proofs();
        let changed = original.clone().with_source_body(ProgramStatement::Skip);
        assert!(changed.open_loop_proof(0, source.clone()).is_err());
        assert!(original.open_loop_proof(0, source).is_ok());
    }

    mod scaling_tests {
        use super::*;
        include!("../../scaling_tests/kernel/termination/loop_evidence.rs");
    }
}
