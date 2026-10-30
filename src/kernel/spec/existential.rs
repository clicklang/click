//! A lowered existential retains each body's requirements under its binder.
//!
//! Keeping these parts separate is necessary before proof checking can defer
//! them until `witness`: a requirement must use the same witness and value
//! path as the body, not an independently proved existential. The legacy
//! checking adapter below still builds the coupled proposition for consumers
//! that have not migrated to scoped requirements.

use super::*;

pub(super) struct ScopedExistential {
    name: String,
    variable: Variable,
    sort: Sort,
    branches: Vec<ScopedExistentialBranch>,
}

pub(super) struct ScopedExistentialBranch {
    proposition: Proposition,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
}

impl ScopedExistentialBranch {
    pub(super) fn from_path(path: SpecPropositionPath) -> Self {
        // Only registered read definitions can be removed. Their loadability
        // and range requirements, and every written condition, remain here.
        let facts = path
            .facts
            .iter()
            .filter(|fact| !fact.is_logical_read_equation())
            .filter_map(|fact| {
                drop_verified_load_definition_conjuncts(fact.proposition().clone())
                    .map(|proposition| fact.clone().with_proposition(proposition))
            })
            .collect();
        let obligations = path
            .obligations
            .iter()
            .filter_map(verified_load_obligation_without_definition)
            .collect();
        Self {
            proposition: path.proposition,
            facts,
            obligations,
        }
    }

    pub(super) fn into_checked_body(self) -> Proposition {
        // Raising a coupled existential writes its domain conjuncts explicitly.
        // Retain each mandatory domain once when that spelling is lowered again.
        // Index only this written body's conjuncts, never ambient facts.
        let mut written = std::collections::BTreeSet::new();
        let mut pending = if self.obligations.is_empty() {
            Vec::new()
        } else {
            vec![&self.proposition]
        };
        while let Some(proposition) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if let Proposition::And(left, right) = proposition {
                pending.extend([left.as_ref(), right.as_ref()]);
            } else {
                if let Some(key) = crate::kernel::proof::proposition_identity_key(proposition) {
                    written.insert(key);
                }
            }
        }
        proposition_and_all(
            self.facts
                .iter()
                .map(|fact| fact.proposition().clone())
                .chain(
                    self.obligations
                        .into_iter()
                        .map(|obligation| obligation.proposition)
                        .filter(|proposition| {
                            !crate::kernel::proof::proposition_identity_key(proposition)
                                .is_some_and(|key| written.contains(&key))
                        }),
                )
                .chain(std::iter::once(self.proposition))
                .collect(),
        )
    }
}

impl ScopedExistential {
    pub(super) fn new(
        name: String,
        variable: Variable,
        sort: Sort,
        paths: Vec<SpecPropositionPath>,
    ) -> Self {
        Self {
            name,
            variable,
            sort,
            branches: paths
                .into_iter()
                .map(ScopedExistentialBranch::from_path)
                .collect(),
        }
    }

    /// Compatibility boundary for the existing proof consumers. Do not move
    /// any requirement outside this binder or combine alternatives' domains:
    /// both would allow the requirement and body to use different witnesses.
    pub(super) fn into_checked_path(self) -> SpecPropositionPath {
        let body = proposition_or_all(
            self.branches
                .into_iter()
                .map(ScopedExistentialBranch::into_checked_body)
                .collect(),
        );
        SpecPropositionPath {
            proposition: Proposition::Exists {
                name: self.name,
                var: self.variable,
                sort: self.sort,
                body: Box::new(body),
            },
            facts: Vec::new().into(),
            obligations: Vec::new(),
            // An introduction below this binder is unreachable until a
            // witness refines the goal. Do not export its head chain.
            introductions: LoweringIntroductions::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn equality(variable: Variable, value: u32) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(Bitvector32Term::Variable(variable)),
                right: Box::new(Bitvector32Term::Constant(value)),
            },
            true,
        )
    }

    fn path(body: Proposition, requirement: Proposition) -> SpecPropositionPath {
        SpecPropositionPath {
            proposition: body,
            facts: Vec::new().into(),
            obligations: vec![
                ProofObligation::verification_condition(requirement)
                    .with_context("the selected witness must be in range"),
            ],
            introductions: LoweringIntroductions::new(),
        }
    }

    #[test]
    fn existential_requirements_keep_their_scope_and_diagnostic() {
        let outer = Variable(200_001);
        let inner = Variable(200_002);
        let domain = Proposition::ForAll {
            name: BinderName::written("i"),
            var: inner,
            sort: Sort::CInt32,
            body: Box::new(Proposition::Implies(
                Box::new(equality(inner, 0)),
                Box::new(equality(outer, 1)),
            )),
        };
        let body = equality(outer, 1);
        let scoped = ScopedExistential::new(
            "k".into(),
            outer,
            Sort::CInt32,
            vec![path(body.clone(), domain.clone())],
        );
        assert_eq!(scoped.branches[0].proposition, body);
        assert_eq!(scoped.branches[0].obligations[0].proposition(), &domain);
        assert_eq!(
            scoped.branches[0].obligations[0].context.as_deref(),
            Some("the selected witness must be in range")
        );
        let checked = scoped.into_checked_path();
        assert!(checked.obligations.is_empty());
        assert!(checked.facts.is_empty());
        assert_eq!(
            checked.proposition,
            Proposition::Exists {
                name: "k".into(),
                var: outer,
                sort: Sort::CInt32,
                body: Box::new(Proposition::And(Box::new(domain), Box::new(body))),
            }
        );
    }

    #[test]
    fn alternative_paths_cannot_supply_each_others_witness_requirements() {
        let variable = Variable(200_003);
        // Each branch is impossible. Separating the disjunction of domains
        // from that of bodies would make both sides satisfiable at 0 or 1.
        let scoped = ScopedExistential::new(
            "k".into(),
            variable,
            Sort::CInt32,
            vec![
                path(equality(variable, 0), equality(variable, 1)),
                path(equality(variable, 1), equality(variable, 0)),
            ],
        );
        let Proposition::Exists { body, .. } = scoped.into_checked_path().proposition else {
            panic!("the requirements and bodies must share one binder");
        };
        for witness in [0, 1, 2] {
            let instantiated = substitute_int32_variable_in_proposition(
                &body,
                variable,
                Bitvector32Term::Constant(witness),
            );
            assert!(PureFactContext::new().proves_exact(&Proposition::Not(Box::new(instantiated))));
        }
    }
}
