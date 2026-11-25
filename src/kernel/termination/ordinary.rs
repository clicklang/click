//! Termination requirements as ordinary, scope-bound propositions.

use super::completion::{ProgramContractGoal, ProgramState, ProvedProgramContracts};
use super::obligations::{TerminationCallObligation, TerminationObligations};
use super::*;
use crate::kernel::proof::PureFactStore;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_SCOPE: AtomicU64 = AtomicU64::new(1);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) enum TerminationAtomKind {
    Local,
    Strict,
    Body,
    Returns,
    Divergence,
    Callbacks,
}

impl TerminationAtomKind {
    pub(crate) fn spelling(self) -> &'static str {
        match self {
            Self::Local => "termination_local",
            Self::Strict => "termination_strict",
            Self::Body => "termination_body",
            Self::Returns => "termination_returns",
            Self::Divergence => "termination_divergence",
            Self::Callbacks => "termination_callbacks",
        }
    }
    pub(crate) fn from_spelling(name: &str) -> Option<Self> {
        [
            Self::Local,
            Self::Strict,
            Self::Body,
            Self::Returns,
            Self::Divergence,
            Self::Callbacks,
        ]
        .into_iter()
        .find(|kind| kind.spelling() == name)
    }
}

/// Canonical presentation retained in the private predicate identity. Decoding
/// does not grant evidence: lowering still requires the current native scope.
pub(crate) fn termination_predicate_spelling(name: &str) -> Option<(TerminationAtomKind, &str)> {
    let (_, body) = name.strip_prefix("\0termination:")?.split_once(':')?;
    let (kind, function) = body.split_once(':')?;
    Some((
        TerminationAtomKind::from_spelling(kind).expect("producer's termination predicate kind"),
        function,
    ))
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) enum TerminationCheck {
    Local(String),
    Component { function: String, strict: bool },
    Callbacks,
}

#[derive(Clone, Debug)]
pub(crate) enum TerminationCause {
    Local {
        function: String,
        call: Option<TerminationRefusal>,
    },
    Refusal(TerminationRefusal),
}

#[derive(Clone, Debug, Default)]
pub(crate) struct TerminationCheckReport {
    pub local: Vec<(String, Option<TerminationRefusal>)>,
    pub functions: Vec<(String, bool, Option<TerminationCause>)>,
    pub unjustified: Vec<String>,
    pub callbacks: Vec<UnsuitableCallback>,
}

/// Immutable producer-owned inputs. Predicate names contain a non-identifier
/// scope brand; Source can name them only through the checked goal raisings.
pub(crate) struct OrdinaryTerminationScope {
    pub(super) obligations: TerminationObligations,
    state: ProgramState,
    requested_subjects: Vec<ProgramFunction>,
    pub(crate) declared_diverging: BTreeSet<String>,
    atoms: BTreeMap<(TerminationAtomKind, String), Proposition>,
    spellings: BTreeMap<String, (TerminationAtomKind, String)>,
    components: Vec<Vec<String>>,
    component_of: BTreeMap<String, usize>,
    goal: Proposition,
    bindings: Vec<ProgramContractGoal>,
}

fn conjunction(mut goals: Vec<Proposition>) -> Proposition {
    if goals.is_empty() {
        return Proposition::condition_is(OldConditionTerm::Constant(true), true);
    }
    while goals.len() > 1 {
        let mut next = Vec::with_capacity(goals.len().div_ceil(2));
        let mut pairs = goals.into_iter();
        while let Some(left) = pairs.next() {
            charge_termination_work(1);
            next.push(match pairs.next() {
                Some(right) => Proposition::And(Box::new(left), Box::new(right)),
                None => left,
            });
        }
        goals = next;
    }
    goals.pop().unwrap()
}

impl OrdinaryTerminationScope {
    pub(super) fn new(
        state: ProgramState,
        obligations: TerminationObligations,
        requested: BTreeSet<String>,
    ) -> Arc<Self> {
        let brand = NEXT_SCOPE.fetch_add(1, Ordering::Relaxed);
        let mut names = obligations
            .functions
            .keys()
            .cloned()
            .chain(requested.iter().cloned())
            .chain(obligations.declared_diverging.iter().cloned())
            .collect::<BTreeSet<_>>();
        for goal in obligations.function_goals.values() {
            charge_termination_work(1);
            for call in &goal.calls {
                charge_termination_work(1);
                match call {
                    TerminationCallObligation::Callee { callee, .. }
                    | TerminationCallObligation::External { callee, .. } => {
                        names.insert(callee.clone());
                    }
                    _ => {}
                }
            }
        }
        names.extend(
            obligations
                .callbacks
                .iter()
                .map(|site| site.callback.clone()),
        );
        let mut atoms = BTreeMap::new();
        let mut spellings = BTreeMap::new();
        for name in &names {
            charge_termination_work(1);
            for kind in [
                TerminationAtomKind::Local,
                TerminationAtomKind::Strict,
                TerminationAtomKind::Body,
                TerminationAtomKind::Returns,
                TerminationAtomKind::Divergence,
            ] {
                charge_termination_work(1);
                let key = format!("\0termination:{brand}:{}:{name}", kind.spelling());
                spellings.insert(key.clone(), (kind, name.clone()));
                atoms.insert(
                    (kind, name.clone()),
                    Proposition::Predicate {
                        name: key,
                        arguments: vec![Term::ExecutionState(Box::new(ExecutionState::new()))],
                    },
                );
            }
        }
        let key = format!("\0termination:{brand}:termination_callbacks:");
        spellings.insert(key.clone(), (TerminationAtomKind::Callbacks, String::new()));
        atoms.insert(
            (TerminationAtomKind::Callbacks, String::new()),
            Proposition::Predicate {
                name: key,
                arguments: vec![Term::ExecutionState(Box::new(ExecutionState::new()))],
            },
        );
        // Same-height edges are the recursion dependencies. Group their
        // connected members once; unrelated leaves at one height stay apart.
        let mut adjacent = BTreeMap::<String, Vec<String>>::new();
        for (name, goal) in &obligations.function_goals {
            adjacent.entry(name.clone()).or_default();
            for callee in &goal.recursive_callees {
                adjacent
                    .entry(name.clone())
                    .or_default()
                    .push(callee.clone());
                adjacent
                    .entry(callee.clone())
                    .or_default()
                    .push(name.clone());
            }
        }
        let mut component_of = BTreeMap::new();
        let mut components = Vec::new();
        for name in obligations.functions.keys() {
            if component_of.contains_key(name) {
                continue;
            }
            let id = components.len();
            let mut members = Vec::new();
            let mut pending = vec![name.clone()];
            while let Some(member) = pending.pop() {
                charge_termination_work(1);
                if component_of.insert(member.clone(), id).is_some() {
                    continue;
                }
                members.push(member.clone());
                pending.extend(
                    adjacent[&member]
                        .iter()
                        .filter(|next| !component_of.contains_key(*next))
                        .cloned(),
                );
            }
            members.sort();
            components.push(members);
        }
        charge_termination_work(state.open.len());
        let bindings = state.open.keys().cloned().collect::<Vec<_>>();
        let declared_diverging = obligations.declared_diverging.clone();
        // Capture publication subjects with the root's selected promises.
        // Completion never scans unrelated function rules.
        let requested_subjects = requested
            .iter()
            .filter_map(|name| {
                charge_termination_work(1);
                let index = obligations.ruled.get(name)?;
                Some(obligations.partial_rules[*index].function.clone())
            })
            .collect();
        let mut scope = Self {
            obligations,
            state,
            requested_subjects,
            declared_diverging,
            atoms,
            spellings,
            components,
            component_of,
            goal: Proposition::condition_is(OldConditionTerm::Constant(true), true),
            bindings,
        };
        let mut goals = Vec::new();
        // Preserve the existing diagnostic priority: marker policy, callbacks,
        // then the selected return requirements.
        for binding in &scope.bindings {
            if let ProgramContractGoal::DivergencePolicy(name) = binding {
                goals.push(scope.atom(TerminationAtomKind::Divergence, name).unwrap());
            }
        }
        goals.push(scope.atom(TerminationAtomKind::Callbacks, "").unwrap());
        for name in &requested {
            goals.push(scope.atom(TerminationAtomKind::Returns, name).unwrap());
        }
        scope.goal = conjunction(goals);
        Arc::new(scope)
    }

    pub(crate) fn goal(&self) -> &Proposition {
        &self.goal
    }
    pub(crate) fn atom(
        &self,
        kind: TerminationAtomKind,
        function: &str,
    ) -> Result<Proposition, String> {
        self.atoms
            .get(&(kind, function.to_string()))
            .cloned()
            .ok_or_else(|| format!("`{function}` is not part of this termination proof"))
    }
    pub(crate) fn spelling(
        &self,
        proposition: &Proposition,
    ) -> Option<(TerminationAtomKind, String)> {
        let Proposition::Predicate { name, arguments } = proposition else {
            return None;
        };
        if !matches!(arguments.as_slice(), [Term::ExecutionState(_)]) {
            return None;
        }
        self.spellings.get(name).cloned()
    }
    fn status(
        &self,
        facts: &PureFactStore,
        kind: TerminationAtomKind,
        name: &str,
    ) -> Result<bool, String> {
        let fact = self.atom(kind, name)?;
        if facts.contains(&fact) {
            return Ok(true);
        }
        if facts.contains(&Proposition::Not(Box::new(fact))) {
            return Ok(false);
        }
        Err(format!(
            "first establish `{}({name:?})` or its negation",
            kind.spelling()
        ))
    }
    fn emit(
        &self,
        output: &mut Vec<Proposition>,
        kind: TerminationAtomKind,
        name: &str,
        value: bool,
    ) {
        let fact = self.atom(kind, name).expect("a generated termination atom");
        output.push(if value {
            fact
        } else {
            Proposition::Not(Box::new(fact))
        });
    }

    /// One checked operation, over its selected generated input and explicit
    /// premise facts. It emits propositions, not a whole-program verdict.
    pub(crate) fn check(
        &self,
        step: &TerminationCheck,
        facts: &PureFactStore,
    ) -> Result<(Vec<Proposition>, TerminationCheckReport), String> {
        let mut output = Vec::new();
        let mut report = TerminationCheckReport::default();
        match step {
            TerminationCheck::Local(name) => {
                if !self.obligations.functions.contains_key(name) {
                    return Err(format!("`{name}` has no body in this termination proof"));
                }
                if self.status(facts, TerminationAtomKind::Local, name).is_ok() {
                    return Ok((output, report));
                }
                let result = self
                    .obligations
                    .prove_local_descent(name)
                    .map_err(|e| format!("could not certify C termination: {e}"))?;
                self.emit(
                    &mut output,
                    TerminationAtomKind::Local,
                    name,
                    result.is_none(),
                );
                report.local.push((name.clone(), result));
            }
            TerminationCheck::Callbacks => {
                if self
                    .status(facts, TerminationAtomKind::Callbacks, "")
                    .is_ok()
                {
                    return Ok((output, report));
                }
                for site in &self.obligations.callbacks {
                    charge_termination_work(1);
                    let returns = if self
                        .obligations
                        .assumed_terminating
                        .contains(&site.callback)
                    {
                        true
                    } else {
                        self.status(facts, TerminationAtomKind::Strict, &site.callback)?
                    };
                    if !returns {
                        report.callbacks.push(UnsuitableCallback {
                            taker: site.taker.clone(),
                            callback: site.callback.clone(),
                        });
                    }
                }
                self.emit(
                    &mut output,
                    TerminationAtomKind::Callbacks,
                    "",
                    report.callbacks.is_empty(),
                );
            }
            TerminationCheck::Component { function, strict } => {
                let public = if *strict {
                    TerminationAtomKind::Strict
                } else {
                    TerminationAtomKind::Returns
                };
                let Some(&component) = self.component_of.get(function) else {
                    let atom = self.atom(public, function)?;
                    let value = self.obligations.assumed_terminating.contains(function);
                    output.push(if value {
                        atom
                    } else {
                        Proposition::Not(Box::new(atom))
                    });
                    if !strict {
                        self.emit(&mut output, TerminationAtomKind::Body, function, value);
                        self.emit(
                            &mut output,
                            TerminationAtomKind::Divergence,
                            function,
                            !value,
                        );
                    }
                    report.functions.push((
                        function.clone(),
                        *strict,
                        (!value).then(|| {
                            TerminationCause::Refusal(TerminationRefusal::Callee {
                                callee: function.clone(),
                            })
                        }),
                    ));
                    return Ok((output, report));
                };
                let members = &self.components[component];
                let mut returning = BTreeSet::new();
                let mut causes = BTreeMap::new();
                let mut callers = BTreeMap::<String, Vec<String>>::new();
                let mut pending = Vec::new();
                for name in members {
                    charge_termination_work(1);
                    let local = self.status(facts, TerminationAtomKind::Local, name)?;
                    let mut call_refusal = None;
                    for call in &self.obligations.function_goals[name].calls {
                        charge_termination_work(1);
                        match call {
                            TerminationCallObligation::Callee {
                                callee,
                                recursive: true,
                            } => {
                                callers
                                    .entry(callee.clone())
                                    .or_default()
                                    .push(name.clone());
                            }
                            TerminationCallObligation::Callee {
                                callee,
                                recursive: false,
                            } => {
                                if !self.status(facts, public, callee)? && call_refusal.is_none() {
                                    call_refusal = Some(TerminationRefusal::Callee {
                                        callee: callee.clone(),
                                    });
                                }
                            }
                            TerminationCallObligation::External { callee, assumed } => {
                                if !assumed && call_refusal.is_none() {
                                    call_refusal = Some(TerminationRefusal::Callee {
                                        callee: callee.clone(),
                                    });
                                }
                            }
                            TerminationCallObligation::Indirect {
                                object,
                                diverging_contract,
                            } => {
                                if let Some(contract) = diverging_contract {
                                    if call_refusal.is_none()
                                        || matches!(
                                            call_refusal,
                                            Some(TerminationRefusal::IndirectCall { .. })
                                        )
                                    {
                                        call_refusal =
                                            Some(TerminationRefusal::DivergingContract {
                                                object: object.clone(),
                                                contract: contract.clone(),
                                            });
                                    }
                                } else if (*strict
                                    || !self.status(facts, TerminationAtomKind::Callbacks, "")?)
                                    && call_refusal.is_none()
                                {
                                    call_refusal = Some(TerminationRefusal::IndirectCall {
                                        object: object.clone(),
                                    });
                                }
                            }
                        }
                    }
                    if !local || call_refusal.is_some() {
                        causes.insert(
                            name.clone(),
                            if !local {
                                TerminationCause::Local {
                                    function: name.clone(),
                                    call: call_refusal,
                                }
                            } else {
                                TerminationCause::Refusal(call_refusal.unwrap())
                            },
                        );
                        pending.push(name.clone());
                    } else {
                        returning.insert(name.clone());
                    }
                }
                while let Some(refused) = pending.pop() {
                    for caller in callers.remove(&refused).unwrap_or_default() {
                        charge_termination_work(1);
                        if returning.remove(&caller) {
                            causes.insert(
                                caller.clone(),
                                TerminationCause::Refusal(TerminationRefusal::Callee {
                                    callee: refused.clone(),
                                }),
                            );
                            pending.push(caller);
                        }
                    }
                }
                for name in members {
                    let body_returns = returning.contains(name);
                    let declared = self.declared_diverging.contains(name);
                    self.emit(&mut output, public, name, body_returns && !declared);
                    if !strict {
                        self.emit(&mut output, TerminationAtomKind::Body, name, body_returns);
                        self.emit(
                            &mut output,
                            TerminationAtomKind::Divergence,
                            name,
                            !body_returns,
                        );
                        if body_returns && declared {
                            report.unjustified.push(name.clone());
                        }
                    }
                    let cause = if body_returns && declared {
                        Some(TerminationCause::Refusal(
                            TerminationRefusal::DeclaredDiverging,
                        ))
                    } else {
                        causes.remove(name)
                    };
                    report.functions.push((name.clone(), *strict, cause));
                }
            }
        }
        Ok((output, report))
    }

    /// Plan only missing classifications, using exact goal/premise lookups.
    /// Executing the result still uses ordinary checked Source steps.
    pub(crate) fn plan(
        &self,
        goal: &Proposition,
        facts: &PureFactStore,
    ) -> Result<Vec<TerminationCheck>, String> {
        let mut stack = Vec::new();
        let mut propositions = vec![goal];
        while let Some(proposition) = propositions.pop() {
            charge_termination_work(1);
            if crate::instrumentation::deadline_exceeded() {
                return Err("termination proof planning exhausted its solve budget".into());
            }
            match proposition {
                Proposition::And(left, right)
                | Proposition::Or(left, right)
                | Proposition::Implies(left, right) => {
                    propositions.push(right);
                    propositions.push(left);
                }
                Proposition::Not(inner) => propositions.push(inner),
                _ => {
                    if let Some((kind, name)) = self.spelling(proposition) {
                        if self.status(facts, kind, &name).is_ok() {
                            continue;
                        }
                        let step = match kind {
                            TerminationAtomKind::Local => TerminationCheck::Local(name),
                            TerminationAtomKind::Strict => TerminationCheck::Component {
                                function: name,
                                strict: true,
                            },
                            TerminationAtomKind::Callbacks => TerminationCheck::Callbacks,
                            _ => TerminationCheck::Component {
                                function: name,
                                strict: false,
                            },
                        };
                        stack.push((step, false, true));
                    }
                }
            }
        }
        let mut done = BTreeSet::new();
        let mut output = Vec::new();
        while let Some((step, leaving, required)) = stack.pop() {
            charge_termination_work(1);
            if crate::instrumentation::deadline_exceeded() {
                return Err("termination proof planning exhausted its solve budget".into());
            }
            if !required {
                let (kind, name) = match &step {
                    TerminationCheck::Local(name) => (TerminationAtomKind::Local, name.as_str()),
                    TerminationCheck::Component { function, strict } => (
                        if *strict {
                            TerminationAtomKind::Strict
                        } else {
                            TerminationAtomKind::Returns
                        },
                        function.as_str(),
                    ),
                    TerminationCheck::Callbacks => (TerminationAtomKind::Callbacks, ""),
                };
                if self.status(facts, kind, name).is_ok() {
                    continue;
                }
            }
            let step = match step {
                TerminationCheck::Component { function, strict } => TerminationCheck::Component {
                    function: self
                        .component_of
                        .get(&function)
                        .map_or(function.clone(), |id| self.components[*id][0].clone()),
                    strict,
                },
                other => other,
            };
            if done.contains(&step) {
                continue;
            }
            if leaving {
                done.insert(step.clone());
                output.push(step);
                continue;
            }
            stack.push((step.clone(), true, true));
            match step {
                TerminationCheck::Local(_) => {}
                TerminationCheck::Callbacks => {
                    for site in &self.obligations.callbacks {
                        charge_termination_work(1);
                        if !self
                            .obligations
                            .assumed_terminating
                            .contains(&site.callback)
                        {
                            stack.push((
                                TerminationCheck::Component {
                                    function: site.callback.clone(),
                                    strict: true,
                                },
                                false,
                                false,
                            ));
                        }
                    }
                }
                TerminationCheck::Component { function, strict } => {
                    if let Some(&component) = self.component_of.get(&function) {
                        for name in &self.components[component] {
                            charge_termination_work(1);
                            stack.push((TerminationCheck::Local(name.clone()), false, false));
                            for call in &self.obligations.function_goals[name].calls {
                                charge_termination_work(1);
                                match call {
                                    TerminationCallObligation::Callee {
                                        callee,
                                        recursive: false,
                                    } => stack.push((
                                        TerminationCheck::Component {
                                            function: callee.clone(),
                                            strict,
                                        },
                                        false,
                                        false,
                                    )),
                                    TerminationCallObligation::Indirect {
                                        diverging_contract: None,
                                        ..
                                    } if !strict => {
                                        stack.push((TerminationCheck::Callbacks, false, false))
                                    }
                                    _ => {}
                                }
                            }
                        }
                    }
                }
            }
        }
        Ok(output)
    }

    pub(in crate::kernel) fn finish(&self) -> ProvedProgramContracts {
        // The ordinary proof was opened on exactly `self.goal`; its completion
        // owns these bindings. This is publication, with no new requirements.
        let mut state = self.state.clone();
        for binding in &self.bindings {
            state.retire(binding);
        }
        charge_termination_work(self.requested_subjects.len());
        let rules = self
            .requested_subjects
            .iter()
            .map(|function| VerifiedFunctionTerminationRule {
                function: function.clone(),
            })
            .collect();
        ProvedProgramContracts {
            proof: state.proof,
            bodies: state.bodies,
            rules,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::proof::{
        OutcomeProofState, ProofObject, ProofObligation, PropositionKnownContext,
    };
    type Proof = ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()>;

    fn scope(size: usize) -> Arc<OrdinaryTerminationScope> {
        scope_requested(
            size,
            (0..size).map(|index| format!("leaf{index}")).collect(),
        )
    }

    fn scope_requested(size: usize, requested: BTreeSet<String>) -> Arc<OrdinaryTerminationScope> {
        let rules = (0..size)
            .map(|index| VerifiedFunctionRule {
                pointer_result: None,
                function: ProgramFunction::new(
                    ProgramType::Void,
                    format!("leaf{index}"),
                    vec![],
                    ProgramStatement::Skip,
                ),
                descent_completion: None,
                concrete_loop_exits: None,
                loop_semantics: LoopSemantics::ApplyVerifiedRules,
                checked_callees: None,
                applied_tactics: Default::default(),
            })
            .collect::<Vec<_>>();
        let owner = ProgramContractProof::open(requested, BTreeSet::new(), &BTreeSet::new());
        owner
            .generate_termination(ProgramTerminationInputs {
                independent: crate::kernel::IndependentTerminationInputs {
                    rules: &rules,
                    bodies: &[],
                },
                plans: &[],
                assumed_terminating: &BTreeSet::new(),
                diverging_contracts: &BTreeSet::new(),
                has_unselected_functions: false,
            })
            .unwrap_or_else(|_| panic!("leaf requirements"))
            .into_ordinary_scope()
    }

    #[test]
    fn native_root_finishes_only_after_ordinary_proof_completion() {
        let scope = scope(2);
        let mut proof = Proof::for_program_termination((), scope.clone(), ());
        assert!(proof.finish_program_termination().is_err());
        for step in scope.plan(scope.goal(), &PureFactStore::default()).unwrap() {
            proof = proof.check_termination(&step).unwrap().0;
        }
        assert!(
            proof.finish_program_termination().is_err(),
            "facts do not complete the root goal"
        );
        proof = proof
            .apply_known(PropositionKnownContext::Exact)
            .unwrap_or_else(|_| panic!("checked termination facts close the root"));
        assert!(
            proof
                .with_termination_context(scope)
                .finish_program_termination()
                .is_err(),
            "nested contexts cannot publish a program proof"
        );
        let completed = proof.finish_program_termination().unwrap().complete();
        assert_eq!(completed.into_termination_rules().len(), 2);
    }

    #[test]
    fn another_scope_cannot_supply_termination_premises() {
        let first = scope(1);
        let second = scope(1);
        let facts = PureFactStore::default()
            .with_fact(first.atom(TerminationAtomKind::Local, "leaf0").unwrap());
        assert!(
            second
                .check(
                    &TerminationCheck::Component {
                        function: "leaf0".into(),
                        strict: false
                    },
                    &facts
                )
                .is_err()
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/termination/ordinary.rs");
    }
}
