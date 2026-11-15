//! Program termination is an ordinary prerequisite of contract completion.
//! Body proofs expose partial rules for modular execution; this owner is the
//! only operation that turns those pending bodies into completed contracts.

use super::*;
use crate::kernel::ContractBodyProof;
use crate::kernel::proof::{BranchId, ProofBranch, ProofBranchState, ProofFacts, ProofObject};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) enum ProgramContractGoal {
    Program,
    Returns(String),
    DivergencePolicy(String),
    CallbackSafety,
    Body { ordinal: usize, function: String },
    BodyOpening,
}

type ProgramProof = ProofObject<(), ProgramContractGoal, ()>;

/// Opened from declarations, before any function body executes. All global
/// requirements belong here, rather than being discovered after completion.
pub(crate) struct ProgramContractProof {
    bodies: ProgramContractBodies,
    requested: BTreeSet<String>,
    declared_diverging: BTreeSet<String>,
}

/// Shared only with the actual function-proof session. Synthetic one-call
/// proofs create fresh sessions without this program owner.
#[derive(Clone)]
pub(crate) struct ProgramContractBodies(Arc<std::sync::Mutex<Option<ProgramState>>>);

impl std::fmt::Debug for ProgramContractBodies {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("ProgramContractBodies")
    }
}
impl PartialEq for ProgramContractBodies {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for ProgramContractBodies {}

struct ProgramState {
    proof: ProgramProof,
    open: BTreeMap<ProgramContractGoal, BranchId>,
    pending_bodies: BTreeMap<usize, String>,
    bodies: Vec<Arc<ContractBodyProof>>,
    next_body: usize,
}

/// Captured by the native root constructor. Surface cannot publish a body or
/// redirect the root's completion to another program.
#[derive(Clone)]
pub(in crate::kernel) struct ProgramBodyOwner {
    parent: ProgramContractBodies,
    goal: ProgramContractGoal,
}

fn branch(goal: ProgramContractGoal) -> ProofBranch<ProgramContractGoal, ()> {
    ProofBranch::new(
        goal,
        ProofBranchState {
            facts: ProofFacts::default(),
            unfolded_predicates: Default::default(),
            execution: None,
        },
    )
}

impl ProgramContractBodies {
    pub(in crate::kernel) fn open_body(&self, function: String) -> ProgramBodyOwner {
        charge_termination_work(1);
        let mut state = self.0.lock().expect("program contract root");
        let state = state
            .as_mut()
            .expect("body opening precedes program completion");
        let ordinal = state.next_body;
        state.next_body += 1;
        let goal = ProgramContractGoal::Body {
            ordinal,
            function: function.clone(),
        };
        let opening = state
            .open
            .remove(&ProgramContractGoal::BodyOpening)
            .expect("body opening remains open");
        let (proof, ids) = state
            .proof
            .focus_open_branch(opening)
            .unwrap_or_else(|_| panic!("the body-opening index addresses its branch"))
            .replace_focused_with_checked_branches(vec![
                branch(goal.clone()),
                branch(ProgramContractGoal::BodyOpening),
            ])
            .unwrap_or_else(|_| panic!("the body-opening branch is open"));
        state.proof = proof;
        state.open.insert(goal.clone(), ids[0]);
        state.open.insert(ProgramContractGoal::BodyOpening, ids[1]);
        state.pending_bodies.insert(ordinal, function);
        ProgramBodyOwner {
            parent: self.clone(),
            goal,
        }
    }
}

impl ProgramBodyOwner {
    pub(in crate::kernel) fn publish(&self, body: Arc<ContractBodyProof>) {
        let mut state = self.parent.0.lock().expect("program contract root");
        let state = state.as_mut().expect("the parent program is open");
        state.retire(&self.goal);
        let ProgramContractGoal::Body { ordinal, .. } = &self.goal else {
            unreachable!();
        };
        state.pending_bodies.remove(ordinal);
        state.bodies.push(body);
    }
}

impl ProgramState {
    fn retire(&mut self, goal: &ProgramContractGoal) {
        charge_termination_work(1);
        let id = self.open.remove(goal).expect("a declared program goal");
        self.proof = self
            .proof
            .focus_open_branch(id)
            .unwrap_or_else(|_| panic!("the program goal index addresses its open branch"))
            .publish_checked_focused_result((), None, vec![], vec![])
            .unwrap_or_else(|_| panic!("the selected program goal is open"));
    }
}

pub(crate) struct ProgramTerminationInputs<'a> {
    pub partial_rules: &'a [VerifiedFunctionRule],
    pub plans: &'a [FunctionTerminationPlan],
    pub inline_bodies: &'a [&'a ProgramFunction],
    pub assumed_terminating: &'a BTreeSet<String>,
    pub diverging_contracts: &'a BTreeSet<String>,
    pub has_unselected_functions: bool,
}

pub(crate) enum ProgramContractFailure {
    Analysis(TerminationError),
    MissingReturnEvidence(String),
    UnfinishedBody(String),
    Obligation {
        goal: ProgramContractGoal,
        verdicts: Box<TerminationVerdicts>,
    },
}

/// Full completion: ordinary body proofs and the program's closed termination
/// root travel together. No caller supplies a verdict or completion receipt.
pub(crate) struct CompletedProgramContracts {
    _proof: ProgramProof,
    _bodies: Vec<Arc<ContractBodyProof>>,
    rules: Vec<VerifiedFunctionTerminationRule>,
}

impl CompletedProgramContracts {
    pub(crate) fn into_termination_rules(self) -> Vec<VerifiedFunctionTerminationRule> {
        self.rules
    }
}

impl ProgramContractProof {
    pub(crate) fn open(
        requested: BTreeSet<String>,
        declared_diverging: BTreeSet<String>,
        bodyless_declarations: &BTreeSet<String>,
    ) -> Self {
        let goals = requested
            .iter()
            .cloned()
            .map(ProgramContractGoal::Returns)
            .chain(
                declared_diverging
                    .difference(bodyless_declarations)
                    .cloned()
                    .map(ProgramContractGoal::DivergencePolicy),
            )
            .chain([
                ProgramContractGoal::CallbackSafety,
                ProgramContractGoal::BodyOpening,
            ])
            .collect::<Vec<_>>();
        let root = ProgramProof::root((), branch(ProgramContractGoal::Program));
        let (proof, ids) = root
            .replace_focused_with_checked_branches(goals.iter().cloned().map(branch).collect())
            .unwrap_or_else(|_| panic!("the program root was just opened"));
        Self {
            bodies: ProgramContractBodies(Arc::new(std::sync::Mutex::new(Some(ProgramState {
                proof,
                open: goals.into_iter().zip(ids).collect(),
                pending_bodies: BTreeMap::new(),
                bodies: Vec::new(),
                next_body: 0,
            })))),
            requested,
            declared_diverging,
        }
    }

    pub(crate) fn bodies(&self) -> ProgramContractBodies {
        self.bodies.clone()
    }

    /// The implicit program closer discharges the already declared goals with
    /// the existing SCC/descent operation. This constructs the successor;
    /// Source never checks a completed contract for further requirements.
    pub(crate) fn complete(
        self,
        inputs: ProgramTerminationInputs<'_>,
    ) -> Result<CompletedProgramContracts, ProgramContractFailure> {
        let mut state = self
            .bodies
            .0
            .lock()
            .expect("program contract root")
            .take()
            .expect("the program completes once");
        if let Some((_, function)) = state.pending_bodies.first_key_value() {
            return Err(ProgramContractFailure::UnfinishedBody(function.clone()));
        }
        // These are this scope's native body outputs, including startup and
        // source-only contracts that deliberately expose no modular rule.
        let mut subjects = inputs
            .partial_rules
            .iter()
            .map(|rule| {
                charge_termination_work(1);
                (rule.function.name().to_string(), rule.clone())
            })
            .collect::<BTreeMap<_, _>>();
        let mut loop_rules = BTreeMap::<String, Vec<VerifiedLoopRule>>::new();
        for body in &state.bodies {
            charge_termination_work(body.loop_rules().len() + 1);
            let rule = body.termination_rule();
            let name = rule.function.name().to_string();
            loop_rules
                .entry(name.clone())
                .or_default()
                .extend_from_slice(body.loop_rules());
            subjects.insert(name, rule.clone());
        }
        let rules = subjects.into_values().collect::<Vec<_>>();
        let heights = program_termination_height_plan(&rules, inputs.inline_bodies);
        let mut plans = inputs.plans.to_vec();
        let plan_indices = plans
            .iter()
            .enumerate()
            .map(|(index, plan)| {
                charge_termination_work(1);
                (plan.function_name().to_string(), index)
            })
            .collect::<BTreeMap<_, _>>();
        let verdicts = loop {
            let verdicts = program_verified_function_termination_rules(
                &rules,
                &plans,
                &loop_rules,
                inputs.inline_bodies,
                &heights,
                inputs.assumed_terminating,
                &self.declared_diverging,
                inputs.diverging_contracts,
            );
            let Err(error) = &verdicts else {
                break verdicts;
            };
            // In a targeted run, the assumed functions may break a recursive
            // cycle. Its measure belongs to the run selecting the whole cycle.
            let retried = inputs.has_unselected_functions
                && error.is_superfluous_recursive_measure()
                && error.function().is_some_and(|function| {
                    plan_indices
                        .get(function)
                        .is_some_and(|&index| plans[index].recursive_measure.take().is_some())
                });
            if !retried {
                break verdicts;
            }
        }
        .map_err(ProgramContractFailure::Analysis)?;

        let failed = verdicts
            .unjustified_diverging
            .iter()
            .map(|name| ProgramContractGoal::DivergencePolicy(name.clone()))
            .find(|goal| state.open.contains_key(goal))
            .or_else(|| {
                (!verdicts.unsuitable_callbacks.is_empty())
                    .then_some(ProgramContractGoal::CallbackSafety)
            });
        let refused = || {
            let mut first = None;
            for name in &self.requested {
                charge_termination_work(1);
                if let Some(refusal) = verdicts.refusals.get(name) {
                    if !matches!(refusal, TerminationRefusal::Callee { .. }) {
                        return Some(ProgramContractGoal::Returns(name.clone()));
                    }
                    first.get_or_insert_with(|| ProgramContractGoal::Returns(name.clone()));
                }
            }
            first
        };
        if let Some(goal) = failed.or_else(refused) {
            return Err(ProgramContractFailure::Obligation {
                goal,
                verdicts: Box::new(verdicts),
            });
        }
        let returning = verdicts
            .rules
            .iter()
            .map(|rule| {
                charge_termination_work(1);
                rule.function.name()
            })
            .collect::<BTreeSet<_>>();
        for name in &self.requested {
            charge_termination_work(1);
            if !returning.contains(name.as_str()) && !inputs.assumed_terminating.contains(name) {
                return Err(ProgramContractFailure::MissingReturnEvidence(name.clone()));
            }
        }
        // Each success is the direct output of this owner's analysis. These
        // are not caller-supplied receipts to revalidate or reconstruct.
        let goals = state.open.keys().cloned().collect::<Vec<_>>();
        for goal in goals {
            state.retire(&goal);
        }
        Ok(CompletedProgramContracts {
            _proof: state.proof,
            _bodies: state.bodies,
            rules: verdicts.rules,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rule(name: &str, body: ProgramStatement) -> VerifiedFunctionRule {
        VerifiedFunctionRule {
            pointer_result: None,
            function: ProgramFunction::new(ProgramType::Void, name, vec![], body),
            loop_semantics: LoopSemantics::ApplyVerifiedRules,
            checked_callees: None,
            applied_tactics: Default::default(),
        }
    }

    fn finish(
        owner: ProgramContractProof,
        rules: &[VerifiedFunctionRule],
    ) -> Result<CompletedProgramContracts, ProgramContractFailure> {
        owner.complete(ProgramTerminationInputs {
            partial_rules: rules,
            plans: &[],
            inline_bodies: &[],
            assumed_terminating: &BTreeSet::new(),
            diverging_contracts: &BTreeSet::new(),
            has_unselected_functions: false,
        })
    }

    #[test]
    fn program_goals_exist_before_execution_and_completion_closes_the_native_root() {
        let owner = ProgramContractProof::open(
            BTreeSet::from(["caller".into(), "callee".into()]),
            BTreeSet::new(),
            &BTreeSet::new(),
        );
        {
            let state = owner.bodies.0.lock().unwrap();
            let state = state.as_ref().unwrap();
            assert!(state.proof.completion().is_none());
            assert_eq!(state.open.len(), 4);
        }
        let completed = finish(
            owner,
            &[
                rule("caller", crate::kernel::program_call("callee", vec![])),
                rule("callee", ProgramStatement::Skip),
            ],
        )
        .unwrap_or_else(|_| panic!("the call chain terminates"));
        assert!(completed._proof.completion().is_some());
        assert_eq!(completed.into_termination_rules().len(), 2);
    }

    #[test]
    fn a_partial_body_cannot_complete_with_an_unranked_loop() {
        let owner = ProgramContractProof::open(
            BTreeSet::from(["spin".into()]),
            BTreeSet::new(),
            &BTreeSet::new(),
        );
        let result = finish(
            owner,
            &[rule(
                "spin",
                crate::kernel::program_while(
                    crate::kernel::program_expression::int32_literal(1),
                    vec![Proposition::ConditionIs(
                        ConditionTerm::Constant(true),
                        true,
                    )],
                    ProgramStatement::Skip,
                ),
            )],
        );
        let Err(ProgramContractFailure::Obligation { goal, verdicts }) = result else {
            panic!("termination is required before contract completion");
        };
        assert_eq!(goal, ProgramContractGoal::Returns("spin".into()));
        assert_eq!(
            verdicts.refusals["spin"],
            TerminationRefusal::UnrankedLoop { index: 0 }
        );
    }

    #[test]
    fn divergence_policy_closes_only_for_a_justified_marker() {
        let open = || {
            ProgramContractProof::open(
                BTreeSet::new(),
                BTreeSet::from(["spin".into()]),
                &BTreeSet::new(),
            )
        };
        assert!(matches!(
            finish(open(), &[rule("spin", ProgramStatement::Skip)]),
            Err(ProgramContractFailure::Obligation {
                goal: ProgramContractGoal::DivergencePolicy(_),
                ..
            })
        ));
        let completed = finish(
            open(),
            &[rule(
                "spin",
                crate::kernel::program_while(
                    crate::kernel::program_expression::int32_literal(1),
                    vec![Proposition::ConditionIs(
                        ConditionTerm::Constant(true),
                        true,
                    )],
                    ProgramStatement::Skip,
                ),
            )],
        )
        .unwrap_or_else(|_| panic!("a justified diverges contract can complete"));
        assert!(completed._proof.completion().is_some());
        assert!(completed.into_termination_rules().is_empty());
    }

    #[test]
    fn absent_evidence_is_an_open_return_obligation() {
        let owner = ProgramContractProof::open(
            BTreeSet::from(["missing".into()]),
            BTreeSet::new(),
            &BTreeSet::new(),
        );
        assert!(
            matches!(finish(owner, &[]), Err(ProgramContractFailure::MissingReturnEvidence(name)) if name == "missing")
        );
    }
}

#[cfg(test)]
mod scaling_tests {
    use super::*;
    include!("../../scaling_tests/kernel/termination/completion.rs");
}
