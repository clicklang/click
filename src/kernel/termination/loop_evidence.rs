//! Bind loop evidence before executing its proof, never at termination consumption.
use super::*;

/// One flat executable-shape stream, with a direct range per source loop.
/// Nested loop bodies share ranges instead of cloning their subtrees.
#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct LoopSourceIndex {
    loops: Vec<std::ops::Range<usize>>,
    shape: Vec<ShapeHead>,
    addressed: BTreeSet<BindingName>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ShapeHead {
    Sequence(usize),
    If(ProgramExpression),
    Loop {
        has_update: bool,
        test_position: LoopTestPosition,
        backedge_target: Option<ControlTargetId>,
        natural_exit_target: Option<ControlTargetId>,
    },
    Switch(ProgramExpression, Vec<Option<u32>>),
    Try(BindingName, bool),
    Leaf(ProgramStatement),
}

impl ShapeHead {
    fn of(statement: &ProgramStatement) -> Self {
        charge_termination_work(1);
        match statement {
            ProgramStatement::Seq(statements) => Self::Sequence(statements.len()),
            ProgramStatement::If { condition, .. } => Self::If(condition.clone()),
            ProgramStatement::Loop {
                test: loop_test,
                update,
                backedge_target,
                natural_exit_target,
                ..
            } => Self::Loop {
                has_update: update.is_some(),
                test_position: loop_test.position,
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
        ProgramStatement::Loop {
            test: loop_test,
            update,
            body,
            ..
        } => program_loop_regions(body, update.as_deref(), Some(loop_test)).all(visit),
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
        ProgramStatement::ThrowOpaque(_)
        | ProgramStatement::Skip
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
                has_update: false,
                test_position: LoopTestPosition::BeforeBody,
                backedge_target: Some(target),
                natural_exit_target: exit,
            });
            index
                .shape
                .push(ShapeHead::Leaf(ProgramStatement::LoopTest {
                    condition: crate::kernel::program_expression::int32_literal(1),
                    aggregate_steps: Vec::new(),
                }));
        }
        index.collect(body);
        if natural.is_some() {
            index.loops[0].end = index.shape.len();
        }
        index
    }
    fn collect(&mut self, statement: &ProgramStatement) {
        let start = self.shape.len();
        let loop_index = if matches!(statement, ProgramStatement::Loop { .. }) {
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
    pub(in crate::kernel) calls: Arc<BTreeSet<String>>,
    pub index: usize,
    pub measure: Option<LoopTerminationMeasure>,
    end: usize,
    bare_descendants: BTreeSet<usize>,
    framed_descendants: BTreeSet<usize>,
    mode: LoopSemantics,
}

impl LoopEvidence {
    pub(in crate::kernel) fn executed_under(mut self, mode: LoopSemantics) -> Self {
        self.mode = mode;
        self
    }
}

fn nested_loop_modes(
    statement: &ProgramStatement,
    next: &mut usize,
    bare: &mut BTreeSet<usize>,
    framed: &mut BTreeSet<usize>,
    summary: bool,
) {
    fn visit(
        statement: &ProgramStatement,
        next: &mut usize,
        bare: &mut BTreeSet<usize>,
        framed: &mut BTreeSet<usize>,
        routes: [bool; 2],
        summary_head: bool,
        constrain_descendants: bool,
    ) {
        charge_termination_work(1);
        let mut descendants = routes;
        if let ProgramStatement::Loop {
            invariant,
            invariant_checks,
            effect_checks,
            resource_specs,
            ranking_measures,
            structural_measure,
            ..
        } = statement
        {
            let index = *next;
            *next += 1;
            if !summary_head {
                let unannotated = invariant.is_empty()
                    && invariant_checks.is_empty()
                    && resource_specs.is_empty()
                    && ranking_measures.is_empty()
                    && structural_measure.is_none();
                let no_effects = effect_checks.is_empty();
                let inherited = effect_checks
                    .iter()
                    .all(|check| check.origin() == LoopEffectOrigin::InheritedResourceDerived);
                let allowed = [
                    routes[0] && unannotated && no_effects,
                    routes[1] && unannotated && inherited,
                ];
                if allowed[0] {
                    bare.insert(index);
                } else if allowed[1] {
                    framed.insert(index);
                }
                // A nested abstraction also hides its descendants. The head
                // of this selected proof is explicitly proved; only nested
                // loops can take the implicit summary route within it.
                if constrain_descendants {
                    descendants = allowed;
                }
            }
        }
        children_all(statement, |child| {
            visit(
                child,
                next,
                bare,
                framed,
                descendants,
                false,
                constrain_descendants,
            );
            true
        });
    }
    visit(
        statement,
        next,
        bare,
        framed,
        [true, true],
        summary,
        summary,
    );
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
        let ProgramStatement::Loop {
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
        let mut end = index;
        let mut bare_descendants = BTreeSet::new();
        let mut framed_descendants = BTreeSet::new();
        nested_loop_modes(
            &statement,
            &mut end,
            &mut bare_descendants,
            &mut framed_descendants,
            true,
        );
        bare_descendants.remove(&index);
        framed_descendants.remove(&index);
        let mut calls = BTreeSet::new();
        statement_calls(&statement, &mut calls);
        Ok(StatementProofInput {
            statement,
            loop_evidence: Some(LoopEvidence {
                calls: Arc::new(calls),
                index,
                measure,
                end,
                bare_descendants,
                framed_descendants,
                mode: LoopSemantics::Verify,
            }),
        })
    }
}

/// The source loop namespace fixed before body proof execution. A completed
/// `ApplyVerifiedRules` body ran every unsummarized loop to exit or avoided it.
/// Summaries keep their separate ranking obligations.
#[derive(Clone, Debug)]
pub(in crate::kernel) struct PreparedLoopExits {
    count: usize,
    bare: BTreeSet<usize>,
    framed: BTreeSet<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) struct ConcreteLoopExits {
    pub count: usize,
    pub(super) concrete: BTreeSet<usize>,
}

impl ConcreteLoopExits {
    pub fn contains(&self, index: &usize) -> bool {
        charge_termination_work(1);
        self.concrete.contains(index)
    }

    pub fn intersect(&self, other: &Self) -> Arc<Self> {
        let concrete = self
            .concrete
            .iter()
            .filter_map(|index| {
                charge_termination_work(1);
                other.concrete.contains(index).then_some(*index)
            })
            .collect();
        Arc::new(Self {
            count: self.count,
            concrete,
        })
    }

    pub(super) fn independent(count: usize, concrete: BTreeSet<usize>) -> Arc<Self> {
        Arc::new(Self { count, concrete })
    }
}

impl PreparedLoopExits {
    pub fn open(function: &ProgramFunction) -> Result<Arc<Self>, String> {
        let source = function
            .loop_source_index
            .0
            .get_or_init(|| LoopSourceIndex::new(function));
        let mut body = LoopSourceIndex::default();
        body.collect(function.body());
        let natural_unwrapped = function.natural_loop_source.is_some()
            && !contains_natural_control_loop(function.body());
        let offset = usize::from(natural_unwrapped);
        if source.loops.len() != body.loops.len() + offset {
            return Err(format!(
                "body opening for `{}` has different source loops",
                function.name()
            ));
        }
        // Compare disjoint outer loop ranges once. Nested loops share those
        // ranges and are not compared again, keeping opening linear in the
        // selected source even for deeply nested loops.
        let mut end = 0;
        for (index, range) in body.loops.iter().enumerate() {
            charge_termination_work(1);
            if range.start < end {
                continue;
            }
            end = range.end;
            let expected = &source.loops[index + offset];
            if source.shape[expected.clone()] != body.shape[range.clone()] {
                return Err(format!(
                    "body opening for `{}` does not match source loop {}",
                    function.name(),
                    index + offset
                ));
            }
        }
        let mut bare = BTreeSet::new();
        let mut framed = BTreeSet::new();
        let mut next = offset;
        nested_loop_modes(function.body(), &mut next, &mut bare, &mut framed, false);
        if natural_unwrapped {
            bare.insert(0);
        }
        Ok(Arc::new(Self {
            count: source.loops.len(),
            bare,
            framed,
        }))
    }

    pub fn unknown(&self) -> Arc<ConcreteLoopExits> {
        Arc::new(ConcreteLoopExits {
            count: self.count,
            concrete: BTreeSet::new(),
        })
    }

    pub fn completed(
        &self,
        mode: LoopSemantics,
        rules: impl Iterator<Item = impl std::borrow::Borrow<VerifiedLoopRule>>,
    ) -> Arc<ConcreteLoopExits> {
        let mut concrete = self
            .bare
            .iter()
            .chain(
                self.framed
                    .iter()
                    .filter(|_| mode == LoopSemantics::ApplyVerifiedRules),
            )
            .map(|index| {
                charge_termination_work(1);
                *index
            })
            .collect::<BTreeSet<_>>();
        for rule in rules {
            charge_termination_work(1);
            match &rule.borrow().loop_evidence {
                Some(evidence) => {
                    for index in evidence.index..evidence.end {
                        charge_termination_work(1);
                        let nested_concrete = evidence.bare_descendants.contains(&index)
                            || (evidence.mode == LoopSemantics::ApplyVerifiedRules
                                && evidence.framed_descendants.contains(&index));
                        if index == evidence.index || !nested_concrete {
                            concrete.remove(&index);
                        }
                    }
                }
                // An independent summary names no source loop. It grants no
                // concrete-execution authority for this body.
                None => concrete.clear(),
            }
        }
        Arc::new(ConcreteLoopExits {
            count: self.count,
            concrete,
        })
    }
}

#[cfg(test)]
pub(super) mod tests {
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
        let ProgramStatement::Loop {
            test: loop_test, ..
        } = &mut different
        else {
            unreachable!()
        };
        *loop_test = LoopTestRegion::expression(int32_literal(1), loop_test.position);
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
                calls: Arc::new(BTreeSet::new()),
                index: 0,
                measure: None,
                end: 1,
                bare_descendants: BTreeSet::new(),
                framed_descendants: BTreeSet::new(),
                mode: LoopSemantics::Verify,
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
        let ProgramStatement::Loop {
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
        let ProgramStatement::Loop {
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

    fn concrete_body(size: usize) -> (crate::kernel::WholeContractRoot, CheckedFunctionExecution) {
        body(size, false)
    }
    pub(in crate::kernel::termination) fn ranked_body(
        size: usize,
    ) -> (crate::kernel::WholeContractRoot, CheckedFunctionExecution) {
        body(size, true)
    }
    fn body(
        size: usize,
        ranked: bool,
    ) -> (crate::kernel::WholeContractRoot, CheckedFunctionExecution) {
        use crate::kernel::proof::*;
        let returning = crate::kernel::program_return(int32_literal(0));
        let tail = if size == 0 {
            returning.clone()
        } else {
            ProgramStatement::Seq(
                ProgramStatementSequence::from_statements(
                    std::iter::once(Arc::new(returning.clone()))
                        .chain((0..size).map(|_| Arc::new(ProgramStatement::Skip))),
                )
                .unwrap(),
            )
        };
        let function = ProgramFunction::new(
            ProgramType::Int32,
            "concrete_body",
            vec![],
            ProgramStatement::seq(Arc::new(loop_statement()), Arc::new(tail)),
        )
        .with_contract(
            vec![],
            vec![],
            vec![],
            vec![FunctionContractClaim::body_safety()],
            true,
        );
        let function = if ranked {
            function
                .with_recursion_measure(vec![RankingComponent::ProgramExpression(int32_literal(0))])
        } else {
            function
        };
        let caller = ExecutionState::new();
        let environment = crate::kernel::program_execution_environment_with_recursion_anchor(
            ExecutionEnvironment::new(),
            &function,
            &caller,
            &[],
        )
        .unwrap();
        let opened = OpenedContractEntry::open(
            &caller,
            &function,
            &[],
            &Vec::<Proposition>::new(),
            &environment,
        )
        .unwrap()
        .open_contract_root(None)
        .unwrap();
        let root = opened.contract_root().unwrap().clone();
        let entry = opened.entry_state().clone();
        let facts = opened.facts().assumptions().clone();
        let mut core = if ranked {
            opened
                .into_execution_core_with_environment(&environment)
                .unwrap()
        } else {
            opened.into_execution_core()
        };
        core.record_condition_transition(
            &function,
            &[],
            Theorem::new(Proposition::ProgramConditionEvaluates {
                state: Box::new(entry.clone()),
                condition: int32_literal(0),
                outcome: ConditionOutcome::Value(false),
            }),
            facts.clone(),
            &[],
            &[],
        )
        .unwrap();
        let outcome = StatementOutcome::Return {
            value: crate::kernel::api::int32(0).into(),
            state: Box::new(entry.clone()),
        };
        if ranked {
            let (execution, _) = crate::kernel::api::prove_symbolic_execution_statement_verification_paths_with_environment_and_loop_rule_using_budget(
                entry, returning, facts.clone(), environment.clone(), ExecutionSemantics::APPLY_VERIFIED_RULES,
                &mut ExecutionBudget::default(),
            );
            let path = &execution.paths[0];
            core.record_statement_transition_with_descent(
                &function,
                &[],
                path,
                facts.clone(),
                &Vec::<ExecutionPureFact>::new(),
            )
            .unwrap();
        } else {
            core.record_statement_transition(
                &function,
                &[],
                Theorem::new(Proposition::ProgramStatementVerifies {
                    state: Box::new(entry),
                    statement: Box::new(returning),
                    outcome: outcome.clone(),
                }),
                facts.clone(),
                &Vec::<ExecutionPureFact>::new(),
                &[],
            )
            .unwrap();
        }
        let (outcome, obligations) = crate::kernel::program_function_outcome_from_statement_outcome(
            &caller,
            &function,
            outcome,
            vec![],
            &facts,
        );
        let candidates = crate::kernel::program_function_execution_candidates_from_outcomes(
            caller,
            function.clone(),
            vec![],
            vec![(outcome, vec![], obligations)],
        );
        let execution = core
            .checked_function_execution(
                &candidates,
                &function,
                facts,
                environment,
                ExecutionSemantics::APPLY_VERIFIED_RULES,
                FunctionContractExecutionMode::ExecuteLoops,
            )
            .unwrap();
        (root, execution)
    }

    pub(in crate::kernel::termination) fn completed_body(
        root: &crate::kernel::WholeContractRoot,
        execution: CheckedFunctionExecution,
        rules: Vec<VerifiedLoopRule>,
    ) -> crate::kernel::CompletedContractExecution {
        use crate::kernel::proof::*;
        let core = execution.open_outcome(0).unwrap();
        let mut closing = crate::kernel::ContractClosingContext::new(&execution).open(0, &core);
        for goal in [
            ContractClosingGoal::ReturnedResources,
            ContractClosingGoal::AllocationLifetime,
            ContractClosingGoal::WriteFootprint,
        ] {
            closing = closing.fixture_close_goal(goal);
        }
        let mut outcome =
            FunctionOutcomeObligation::new(0, Arc::new(OutcomeProofState::new(core, ())));
        outcome.claims = Some(OutcomeClaimGoals::open([], false));
        outcome.closing = Some(closing);
        let proof: ProofObject<
            (),
            crate::kernel::proof::ProofObligation<(), Arc<OutcomeProofState<()>>>,
            (),
        > = ProofObject::root(
            (),
            ProofBranch::new(
                crate::kernel::proof::ProofObligation::FunctionOutcome(outcome),
                ProofBranchState {
                    facts: ProofFacts::default(),
                    execution: None,
                },
            ),
        );
        let mut owner = proof
            .open_contract_execution(
                execution,
                Some(root),
                std::iter::once(proof.focused_branch()),
            )
            .unwrap();
        proof
            .complete_function_outcome_in_execution(&proof, &mut owner)
            .unwrap()
            .finish_contract_execution(owner)
            .unwrap()
            .with_loop_rules(rules.into())
    }

    #[test]
    fn concrete_exit_authority_is_published_only_by_completed_body_proofs() {
        let (root, execution) = concrete_body(0);
        let attempted = root.begin_attempt();
        completed_body(attempted.root(), execution.clone(), vec![]).publish(false);
        drop(attempted);
        assert!(
            root.finish().is_err(),
            "an abandoned proof publishes no concrete exits"
        );
        let attempted = root.begin_attempt();
        completed_body(attempted.root(), execution, vec![]).publish(false);
        attempted.commit();
        let rule = root.finish().unwrap().to_reusable_rule().unwrap();
        assert!(rule.concrete_loop_exits.as_ref().unwrap().contains(&0));
        let heights = program_termination_height_plan(std::slice::from_ref(&rule), &[]);
        let verdicts = program_verified_function_termination_rules(
            &[rule],
            &[],
            &BTreeMap::new(),
            &[],
            &heights,
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .unwrap();
        assert!(verdicts.refusals.is_empty());
    }

    #[test]
    fn a_summarized_sibling_cannot_inherit_concrete_exit_authority() {
        for reverse in [false, true] {
            let (root, execution) = concrete_body(0);
            let concrete = root.begin_attempt();
            let summarized = root.begin_attempt();
            completed_body(concrete.root(), execution.clone(), vec![]).publish(false);
            let summary = prove(root.open_loop_proof(0, loop_statement()).unwrap());
            completed_body(summarized.root(), execution, vec![summary]).publish(false);
            if reverse {
                summarized.commit();
                concrete.commit();
            } else {
                concrete.commit();
                summarized.commit();
            }
            let rule = root.finish().unwrap().to_reusable_rule().unwrap();
            assert!(!rule.concrete_loop_exits.as_ref().unwrap().contains(&0));
            let heights = program_termination_height_plan(std::slice::from_ref(&rule), &[]);
            let verdicts = program_verified_function_termination_rules(
                &[rule],
                &[],
                &BTreeMap::new(),
                &[],
                &heights,
                &BTreeSet::new(),
                &BTreeSet::new(),
                &BTreeSet::new(),
            )
            .unwrap();
            assert_eq!(
                verdicts.refusals["concrete_body"],
                TerminationRefusal::UnrankedLoop { index: 0 }
            );
        }
    }

    #[test]
    fn body_source_mismatch_is_refused_at_opening() {
        let original = loop_statement();
        let changed =
            crate::kernel::program_while(int32_literal(1), vec![], ProgramStatement::Skip);
        let function = function(original).with_source_body(changed);
        assert!(
            PreparedLoopExits::open(&function)
                .unwrap_err()
                .contains("does not match source loop")
        );
    }

    #[test]
    fn nested_summary_coverage_respects_the_producing_loop_mode() {
        let framed = crate::kernel::program_while_with_invariant_and_effect_checks(
            int32_literal(0),
            vec![],
            vec![],
            vec![LoopEffectCheck::new_with_origin(
                crate::kernel::LoopEffect::Mutable(vec![]),
                crate::kernel::LoopEffectSpan::Whole,
                LoopEffectOrigin::InheritedResourceDerived,
                None,
            )],
            loop_statement(),
        );
        let outer = crate::kernel::program_while(int32_literal(0), vec![], framed);
        let function = function(outer.clone());
        let plan = PreparedLoopExits::open(&function).unwrap();
        let mut rule = prove(function.open_loop_proof(0, outer).unwrap());
        let verified = plan.completed(LoopSemantics::ApplyVerifiedRules, std::iter::once(&rule));
        assert!(!verified.contains(&0));
        assert!(
            !verified.contains(&1),
            "verification may summarize the inherited-frame inner loop"
        );
        assert!(
            !verified.contains(&2),
            "an implicit summary hides its bare descendant"
        );
        rule.loop_evidence = rule
            .loop_evidence
            .map(|evidence| evidence.executed_under(LoopSemantics::ApplyVerifiedRules));
        let concrete = plan.completed(LoopSemantics::ApplyVerifiedRules, std::iter::once(&rule));
        assert!(
            concrete.contains(&1),
            "checked phase execution unrolls an unruled inner loop"
        );
        assert!(concrete.contains(&2));
    }

    mod scaling_tests {
        use super::*;
        include!("../../scaling_tests/kernel/termination/loop_evidence.rs");
    }
}
