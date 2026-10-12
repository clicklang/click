//! `auto` on an `Integer` fact whose atoms observe machine values.
//!
//! The solver reads linear `Integer` claims. A proof about `to_integer(i)`
//! usually also needs what the program knows about `i` itself: `i < n` for
//! two `uint64` values says `to_integer(i) < to_integer(n)`, and a `uint64`
//! is never negative. Those facts reach the solver as the steps a proof would
//! write by hand: each connected machine order fact is carried to `Integer`
//! by its bridge theorem (`uint64_less_than_to_integer`, ...), and each
//! unsigned value's observation gets its type range (`uint64_to_integer_bounds`).
//! The solver then runs over the original and the carried facts, and only
//! the carried facts its certificate cites are kept, so the expansion holds
//! the bridges the proof needs and no others. Every step is an `apply` of a
//! standard theorem or an `Integer` certificate; nothing here is trusted.

use super::wide_arithmetic::{Carrier, Relation, apply, have, relate, relation_parts, to_integer};
use super::*;
use crate::surface::checking::{IntegerRefutation, plan_integer_refutation};

/// The machine type an order fact compares, with the names its bridges use.
#[derive(Clone, Copy, Eq, PartialEq)]
enum MachineOrder {
    Int32,
    Wide(Carrier),
}

impl MachineOrder {
    fn of(proposition: &Proposition) -> Option<Self> {
        if let Some(carrier) = Carrier::of(proposition) {
            return Some(Self::Wide(carrier));
        }
        match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(..)
                | ConditionTerm::Bitvector32SignedLessEqual(..)
                | ConditionTerm::Bitvector32SignedGreaterThan(..)
                | ConditionTerm::Bitvector32SignedGreaterEqual(..),
                _,
            ) => Some(Self::Int32),
            _ => None,
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::Int32 => "int32",
            Self::Wide(carrier) => carrier.name(),
        }
    }

    fn typed_literals(self, expression: &ContractExpression) -> ContractExpression {
        match self {
            Self::Int32 => expression.clone(),
            Self::Wide(carrier) => carrier.typed_literals(expression),
        }
    }

    /// The type range of an unsigned value's observation, when the standard
    /// library states one.
    fn range(self) -> Option<(&'static str, &'static str)> {
        match self {
            Self::Wide(carrier) if carrier.name() == "uint64" => {
                Some(("uint64_to_integer_bounds", "18446744073709551615"))
            }
            _ => None,
        }
    }
}

/// One carried fact: the steps that establish it and its source spelling.
struct Carried {
    steps: Vec<ProofStep>,
    surface: ClickProposition,
}

impl<'a> Proof<'a> {
    /// Close an `Integer` bound goal with the solver after carrying the
    /// connected machine order facts to `Integer`. Any miss leaves the proof
    /// unchanged.
    pub(in crate::surface::proof) fn try_bridged_solver_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        let (Some(goal), Some(surface_goal)) = (self.goal(), self.surface_goal()) else {
            return Ok(None);
        };
        if crate::kernel::proof::integer_arithmetic::integer_affine_claim(goal).is_none() {
            return Ok(None);
        }
        let Some(candidates) =
            crate::surface::planning::proposition_search::solver_connected_premises(
                self.facts().assumptions(),
                goal,
            )
        else {
            return Ok(None);
        };
        let carried = self.carried_machine_facts(&candidates);
        if carried.is_empty() {
            return Ok(None);
        }

        // Establish every carried fact once to learn its kernel form; the
        // solver then picks among them.
        let mut trial = self.clone();
        let mut established: Vec<(Proposition, &Carried)> = Vec::new();
        for item in &carried {
            check_verification_deadline()?;
            let Ok(next) = item
                .steps
                .iter()
                .try_fold(trial.clone(), |proof, step| proof.apply_step(step.clone()))
            else {
                continue;
            };
            let Ok(kernel) = next.lower_cited_surface_proposition(&item.surface, "carried fact")
            else {
                continue;
            };
            trial = next;
            established.push((kernel, item));
        }
        let mut premises = candidates;
        premises.extend(established.iter().map(|(kernel, _)| kernel.clone()));
        for _ in 0..super::smart_closures::SOLVER_SPELLING_ROUNDS {
            check_verification_deadline()?;
            let IntegerRefutation::Proved {
                certificate,
                premises: used,
            } = crate::instrumentation::measure_operation(
                "surface",
                "auto solver",
                "auto solver: bridged integer refutation",
                || plan_integer_refutation(goal, &premises),
            )
            else {
                return Ok(None);
            };
            // Keep only the carried facts the certificate cites, in their
            // order.
            let mut proof = self.clone();
            for (kernel, item) in &established {
                if used.contains(kernel) {
                    for step in &item.steps {
                        match proof.apply_step(step.clone()) {
                            Ok(next) => proof = next,
                            Err(_) => return Ok(None),
                        }
                    }
                }
            }
            let mut pairs = Vec::with_capacity(used.len());
            let mut unspelled = Vec::new();
            for premise in &used {
                if let Some((_, item)) = established.iter().find(|(kernel, _)| kernel == premise) {
                    pairs.push((premise.clone(), item.surface.clone()));
                    continue;
                }
                match proof
                    .resolve_simp_premises(std::slice::from_ref(premise), &[])
                    .and_then(|mut spelled| spelled.pop())
                {
                    Some(pair) => pairs.push(pair),
                    None => unspelled.push(premise.clone()),
                }
            }
            if !unspelled.is_empty() {
                premises.retain(|premise| !unspelled.contains(premise));
                continue;
            }
            let Some(surface) = super::smart_closures::integer_plan_to_surface_certificate(
                &certificate,
                &pairs,
                surface_goal,
            ) else {
                return Ok(None);
            };
            return attempt::candidate_outcome(proof.apply_step(ProofStep::ArithmeticCertificate(
                ArithmeticCertificate::integer(surface),
            )));
        }
        Ok(None)
    }

    /// Close an `Integer` equality goal `l == r` by proving `l <= r` and
    /// `r <= l` with `auto` on each stated fact and joining them with
    /// `equal_from_bounds`. Any miss leaves the proof unchanged.
    pub(in crate::surface::proof) fn try_solver_equality_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        let (Some(goal), Some(surface_goal)) = (self.goal(), self.surface_goal()) else {
            return Ok(None);
        };
        if !crate::kernel::proof::integer_arithmetic::integer_affine_claim(goal).is_some_and(
            |claim| {
                claim.relation
                    == crate::kernel::proof::integer_arithmetic::IntegerAffineRelation::Equal
            },
        ) {
            return Ok(None);
        }
        let ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right,
        } = surface_goal
        else {
            return Ok(None);
        };
        let lower = relate(left.clone(), right.clone(), Relation::LessEqual);
        let upper = relate(right.clone(), left.clone(), Relation::LessEqual);
        let mut proof = self.clone();
        for bound in [&lower, &upper] {
            let Ok(scope) = proof.begin_have(bound.clone()) else {
                return Ok(None);
            };
            let Some(closed) = scope.try_auto_fact_closure()? else {
                return Ok(None);
            };
            let Ok(joined) = closed.join() else {
                return Ok(None);
            };
            proof = joined;
        }
        let certificate = IntegerCertificate {
            nodes: vec![
                IntegerCertificateNode::Premise {
                    index: 0,
                    proposition: lower.clone(),
                    result: lower,
                },
                IntegerCertificateNode::Premise {
                    index: 1,
                    proposition: upper.clone(),
                    result: upper,
                },
                IntegerCertificateNode::EqualityFromBounds {
                    lower: 0,
                    upper: 1,
                    result: surface_goal.clone(),
                },
            ],
            conclusion: 2,
        };
        attempt::candidate_outcome(proof.apply_step(ProofStep::ArithmeticCertificate(
            ArithmeticCertificate::integer(certificate),
        )))
    }

    /// Close a machine order goal `a < b` or `a <= b` by proving its
    /// `Integer` reading with `auto` on the stated fact and carrying it back
    /// with the type's bridge (`uint64_to_integer_less_than_implies_less_than`,
    /// ...). Any miss leaves the proof unchanged.
    pub(in crate::surface::proof) fn try_machine_goal_solver_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        let (Some(goal), Some(surface_goal)) = (self.goal(), self.surface_goal()) else {
            return Ok(None);
        };
        if !matches!(goal, Proposition::ConditionIs(_, true)) {
            return Ok(None);
        }
        let Some(order) = MachineOrder::of(goal) else {
            return Ok(None);
        };
        let Some((lower, upper, relation, true)) = relation_parts(surface_goal) else {
            return Ok(None);
        };
        let stem = match (order, relation) {
            (_, Relation::LessEqual) => "to_integer_less_equal_implies_less_equal",
            // `int32` has no strict converse bridge in the standard library.
            (MachineOrder::Wide(_), Relation::Less) => "to_integer_less_than_implies_less_than",
            _ => return Ok(None),
        };
        let lower = order.typed_literals(&lower);
        let upper = order.typed_literals(&upper);
        let observed = relate(to_integer(&lower), to_integer(&upper), relation);
        let scope = match self.begin_have(observed.clone()) {
            Ok(scope) => scope,
            Err(_) => return Ok(None),
        };
        let Some(closed) = scope.try_auto_fact_closure()? else {
            return Ok(None);
        };
        let Ok(proof) = closed.join() else {
            return Ok(None);
        };
        let Ok(applied) = proof.apply_step(apply(
            &format!("{}_{stem}", order.name()),
            vec![lower, upper],
            vec![observed],
        )) else {
            return Ok(None);
        };
        if applied.is_complete() || applied.goal() != self.goal() {
            return Ok(Some(applied));
        }
        Ok(applied.try_direct_logical_closure().ok().flatten())
    }

    /// The `Integer` reading of each connected machine order fact, and the
    /// type range of each unsigned value they mention.
    fn carried_machine_facts(&self, candidates: &[Proposition]) -> Vec<Carried> {
        let mut carried = Vec::new();
        let mut ranged: Vec<ContractExpression> = Vec::new();
        for candidate in candidates {
            let Some(order) = MachineOrder::of(candidate) else {
                continue;
            };
            crate::instrumentation::record_deterministic_work(1);
            let Some(spelled) = self.resolve_simp_premises(std::slice::from_ref(candidate), &[])
            else {
                continue;
            };
            let Some((_, surface)) = spelled.into_iter().next() else {
                continue;
            };
            let Some((lower, upper, relation, _)) = relation_parts(&surface) else {
                continue;
            };
            let stem = match relation {
                Relation::Less => "less_than_to_integer",
                Relation::LessEqual => "less_equal_to_integer",
                Relation::Equal => continue,
            };
            let lower = order.typed_literals(&lower);
            let upper = order.typed_literals(&upper);
            let stated = relate(lower.clone(), upper.clone(), relation);
            let mut steps = Vec::new();
            // A negated or reversed order is first stated the bridge's way
            // round, which is the same fact to the kernel.
            if stated != surface {
                steps.push(have(stated.clone(), vec![ProofStep::Assumption]));
            }
            let observed = relate(to_integer(&lower), to_integer(&upper), relation);
            steps.push(have(
                observed.clone(),
                vec![apply(
                    &format!("{}_{stem}", order.name()),
                    vec![lower.clone(), upper.clone()],
                    vec![stated],
                )],
            ));
            carried.push(Carried {
                steps,
                surface: observed,
            });
            if let Some((theorem, maximum)) = order.range() {
                for value in [lower, upper] {
                    if matches!(to_integer(&value), ContractExpression::IntegerLiteral(_))
                        || ranged.contains(&value)
                    {
                        continue;
                    }
                    ranged.push(value.clone());
                    let bounds = apply(theorem, vec![value.clone()], Vec::new());
                    for bound in [
                        relate(
                            ContractExpression::IntegerLiteral("0".into()),
                            to_integer(&value),
                            Relation::LessEqual,
                        ),
                        relate(
                            to_integer(&value),
                            ContractExpression::IntegerLiteral(maximum.into()),
                            Relation::LessEqual,
                        ),
                    ] {
                        carried.push(Carried {
                            steps: vec![have(bound.clone(), vec![bounds.clone()])],
                            surface: bound,
                        });
                    }
                }
            }
        }
        carried
    }
}
