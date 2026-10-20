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

// Arithmetic subgoals reuse the outer memory search. Nested arithmetic
// scopes preserve that choice until the outermost bridge returns.
thread_local! {
    static ACTIVE_MACHINE_EQUALITY_BRIDGE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

pub(super) fn machine_equality_bridge_active() -> bool {
    ACTIVE_MACHINE_EQUALITY_BRIDGE.with(std::cell::Cell::get)
}

struct MachineEqualityBridgeScope {
    previous: bool,
}

impl MachineEqualityBridgeScope {
    fn enter() -> Self {
        Self {
            previous: ACTIVE_MACHINE_EQUALITY_BRIDGE.with(|active| active.replace(true)),
        }
    }
}

impl Drop for MachineEqualityBridgeScope {
    fn drop(&mut self) {
        ACTIVE_MACHINE_EQUALITY_BRIDGE.with(|active| active.set(self.previous));
    }
}

/// How many rewrites `auto`'s equality search chains before closing.
const REWRITE_DEPTH: usize = 3;

/// How many connected equalities the search offers, and how many checked
/// rewrites it tries in all. A large connected component fails promptly
/// instead of exploring every short chain of its equalities.
const REWRITE_EQUALITIES: usize = 64;
const REWRITE_ATTEMPTS: usize = 256;

/// How many rewritten goals the search offers to `simp`, after the cheap
/// closers miss: `simp` unfolds and computes what a rewrite exposes.
const REWRITE_SIMP_CLOSURES: usize = 8;

/// How many rewrites `auto` tries, each followed by `assumption`, before
/// its solvers: a goal that restates a fact through one equation.
const SINGLE_REWRITES: usize = 16;

/// How many connected constructor equations `auto` pairs.
const CONSTRUCTOR_EQUATIONS: usize = 16;

/// How many connected function facts `auto` reads a goal out of, and how
/// many leaves of one definition's conditional tree it splits down to.
const DEFINITION_FACTS: usize = 16;
const DEFINITION_LEAVES: usize = 16;
/// How many applications at a definition's ends `auto` follows into their
/// own definitions on the way to one end.
const DEFINITION_UNFOLDS: usize = 4;

/// The machine type an order fact compares, with the names its bridges use.
#[derive(Clone, Copy, Eq, PartialEq)]
enum MachineOrder {
    Int32,
    Wide(Carrier),
    /// A 64-bit equality. The kernel's equality does not say whether its
    /// operands are signed, so its bridges are tried for `uint64` and then
    /// `int64`; the other type's application is refused.
    Equal64,
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
            // An `int32` equality; a `uint32` one is refused by the `int32`
            // bridges and left out.
            Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(..), true) => {
                Some(Self::Int32)
            }
            Proposition::ConditionIs(ConditionTerm::Bitvector64Equal(..), true) => {
                Some(Self::Equal64)
            }
            _ => None,
        }
    }

    /// The bridge prefix. `Equal64` reaches a bridge only through
    /// `carriers`.
    fn name(self) -> &'static str {
        match self {
            Self::Int32 => "int32",
            Self::Wide(carrier) => carrier.name(),
            Self::Equal64 => "uint64",
        }
    }

    fn typed_literals(self, expression: &ContractExpression) -> ContractExpression {
        match self {
            Self::Int32 | Self::Equal64 => expression.clone(),
            Self::Wide(carrier) => carrier.typed_literals(expression),
        }
    }

    /// The type range of an unsigned value's observation, when the standard
    /// library states one.
    fn range(self) -> Option<(&'static str, &'static str, &'static str)> {
        match self {
            Self::Int32 => Some((
                "click::integer::int32_to_integer_bounds",
                "-2147483648",
                "2147483647",
            )),
            Self::Wide(carrier) => match carrier.name() {
                "uint64" => Some((
                    "click::integer::uint64_to_integer_bounds",
                    "0",
                    "18446744073709551615",
                )),
                "int64" => Some((
                    "click::integer::int64_to_integer_bounds",
                    "-9223372036854775808",
                    "9223372036854775807",
                )),
                _ => None,
            },
            Self::Equal64 => None,
        }
    }
}

/// One carried fact: how it is established and its source spelling.
struct Carried {
    establish: Establish,
    surface: ClickProposition,
}

enum Establish {
    /// A fixed sequence of steps.
    Steps(Vec<ProofStep>),
    /// The term-by-term observation of `left + right` or `left - right`:
    /// a signed operation once it is defined, which `auto` proves when it is
    /// not already a fact, and an unsigned one once it stays in range.
    Operation {
        operation: ContractExpression,
        left: ContractExpression,
        right: ContractExpression,
        subtract: bool,
    },
}

#[cfg(test)]
thread_local! {
    static BRIDGE_ESTABLISHMENTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

thread_local! {
    // A bridge may ask for this operation's definedness or no-wrap bound.
    // Proving that prerequisite can find the same operation among connected
    // machine facts. Re-entering its bridge cannot establish new evidence.
    static ACTIVE_OPERATION_BRIDGES: std::cell::RefCell<Vec<ContractExpression>> = const { std::cell::RefCell::new(Vec::new()) };
}

struct OperationBridgeScope;

impl OperationBridgeScope {
    fn enter(operation: &ContractExpression) -> Option<Self> {
        ACTIVE_OPERATION_BRIDGES.with(|active| {
            let mut active = active.borrow_mut();
            if active.contains(operation) {
                return None;
            }
            active.push(operation.clone());
            Some(Self)
        })
    }
}

impl Drop for OperationBridgeScope {
    fn drop(&mut self) {
        ACTIVE_OPERATION_BRIDGES.with(|active| {
            active.borrow_mut().pop();
        });
    }
}

impl Carried {
    fn establish<'a>(&self, proof: &Proof<'a>) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        BRIDGE_ESTABLISHMENTS.with(|count| count.set(count.get() + 1));
        match &self.establish {
            Establish::Steps(steps) => Ok(steps
                .iter()
                .try_fold(proof.clone(), |proof, step| proof.apply_step(step.clone()))
                .ok()),
            Establish::Operation {
                operation,
                left,
                right,
                subtract,
            } => {
                let stem = if *subtract { "subtract" } else { "add" };
                let arguments = vec![left.clone(), right.clone()];
                let defined = ClickProposition::Defined {
                    expression: operation.clone(),
                };
                let observe = |proof: &Proof<'a>, name: String, requirement: &ClickProposition| {
                    proof
                        .apply_step(have(
                            self.surface.clone(),
                            vec![apply(&name, arguments.clone(), vec![requirement.clone()])],
                        ))
                        .ok()
                };
                for width in ["int32", "int64"] {
                    let name = format!("{width}_{stem}_to_integer");
                    if let Some(next) = observe(proof, name.clone(), &defined) {
                        return Ok(Some(next));
                    }
                }
                // An unsigned operation that does not wrap.
                let guard = if *subtract {
                    relate(to_integer(right), to_integer(left), Relation::LessEqual)
                } else {
                    relate(
                        ContractExpression::Add(
                            Box::new(to_integer(left)),
                            Box::new(to_integer(right)),
                        ),
                        ContractExpression::IntegerLiteral("18446744073709551615".into()),
                        Relation::LessEqual,
                    )
                };
                if let Some(next) = observe(proof, format!("uint64_{stem}_to_integer"), &guard) {
                    return Ok(Some(next));
                }
                let Some(_operation_scope) = OperationBridgeScope::enter(operation) else {
                    return Ok(None);
                };
                // Not yet known to be defined: prove it, then observe.
                if let Some(next) = proof.prove_stated_fact(&defined)? {
                    for width in ["int32", "int64"] {
                        let name = format!("{width}_{stem}_to_integer");
                        if let Some(observed) = observe(&next, name, &defined) {
                            return Ok(Some(observed));
                        }
                    }
                }
                let Some(next) = proof.prove_stated_fact(&guard)? else {
                    return Ok(None);
                };
                Ok(observe(&next, format!("uint64_{stem}_to_integer"), &guard))
            }
        }
    }
}

/// The type range of a machine value's observation, for each type whose
/// range theorem could apply. The wrong types' applications fail when the
/// fact is established, and are left out.
fn range_items(value: &ContractExpression) -> Vec<Carried> {
    let mut items = Vec::new();
    for (theorem, minimum, maximum) in [
        (
            "click::integer::int32_to_integer_bounds",
            "-2147483648",
            "2147483647",
        ),
        (
            "click::integer::int64_to_integer_bounds",
            "-9223372036854775808",
            "9223372036854775807",
        ),
        (
            "click::integer::uint64_to_integer_bounds",
            "0",
            "18446744073709551615",
        ),
    ] {
        let bounds = apply(theorem, vec![value.clone()], Vec::new());
        for bound in [
            relate(
                integer_literal(minimum),
                to_integer(value),
                Relation::LessEqual,
            ),
            relate(
                to_integer(value),
                integer_literal(maximum),
                Relation::LessEqual,
            ),
        ] {
            items.push(Carried {
                establish: Establish::Steps(vec![have(bound.clone(), vec![bounds.clone()])]),
                surface: bound,
            });
        }
    }
    items
}

/// What `auto`'s rewrite search may still spend.
struct RewriteBudget {
    attempts: usize,
    simp_closures: usize,
}

/// An equality in both directions, each with its kernel form.
fn oriented_forms(
    kernel: Proposition,
    surface: ClickProposition,
) -> Vec<(Proposition, ClickProposition)> {
    // Arithmetic operands need an explicit observation when reparsed under
    // `arithmetic "integer"`. Ordinary equalities retain their source spelling.
    let machine_arithmetic = |term: &Bitvector32Term| {
        matches!(
            term,
            Bitvector32Term::Add(..)
                | Bitvector32Term::Subtract(..)
                | Bitvector32Term::Multiply(..)
                | Bitvector32Term::Int64Add(..)
                | Bitvector32Term::Int64Subtract(..)
                | Bitvector32Term::Int64Multiply(..)
                | Bitvector32Term::UInt64Add(..)
                | Bitvector32Term::UInt64Subtract(..)
                | Bitvector32Term::UInt64Multiply(..)
        )
    };
    let arithmetic = |mut operand: &ContractExpression| {
        loop {
            match operand {
                ContractExpression::Old(inner)
                | ContractExpression::At {
                    expression: inner, ..
                } => operand = inner,
                ContractExpression::Add(..)
                | ContractExpression::Subtract(..)
                | ContractExpression::Multiply(..)
                | ContractExpression::Negate(_) => return true,
                ContractExpression::CFragment(
                    CExpression::Add(..) | CExpression::Subtract(..) | CExpression::Multiply(..),
                ) => return true,
                ContractExpression::CFragment(CExpression::Value(value)) => {
                    return matches!(
                    value.numeric_value(), crate::kernel::integer_c_value!(term) if machine_arithmetic(term));
                }
                _ => return false,
            }
        }
    };
    let mut written = &surface;
    while let ClickProposition::At { proposition, .. } | ClickProposition::Not(proposition) =
        written
    {
        written = proposition;
    }
    let surface = if matches!(written,
        ClickProposition::Comparison { left, right, .. } if arithmetic(left) || arithmetic(right))
    {
        super::smart_closures::observed_native_surface_comparison(&kernel, &surface)
    } else {
        surface
    };
    let reverse = crate::kernel::proof::equality_rewrite::reverse_equality(&kernel).zip(
        super::fixed_state_proofs::reverse_surface_equality(&surface),
    );
    std::iter::once((kernel, surface)).chain(reverse).collect()
}

/// `l == r` for an equality spelled `at(S, l) == at(S, r)` or `at(S, l == r)`.
fn unanchored_equality(surface: &ClickProposition) -> Option<ClickProposition> {
    match surface {
        ClickProposition::At { proposition, .. } => Some(proposition.as_ref().clone()),
        ClickProposition::Comparison {
            left:
                ContractExpression::At {
                    selector: left_selector,
                    expression: left,
                },
            operator,
            right:
                ContractExpression::At {
                    selector: right_selector,
                    expression: right,
                },
        } if left_selector == right_selector => Some(ClickProposition::Comparison {
            left: left.as_ref().clone(),
            operator: *operator,
            right: right.as_ref().clone(),
        }),
        _ => None,
    }
}

/// The two sides of an algebraic equality fact.
fn algebraic_sides(
    fact: &Proposition,
) -> Option<(&crate::kernel::AlgebraicTerm, &crate::kernel::AlgebraicTerm)> {
    match fact {
        Proposition::ConditionIs(ConditionTerm::AlgebraicEqual(left, right), true) => {
            Some((left, right))
        }
        Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) => Some((left, right)),
        _ => None,
    }
}

fn is_constructor(term: &crate::kernel::AlgebraicTerm) -> bool {
    matches!(
        term.node,
        crate::kernel::AlgebraicTermNode::Constructor { .. }
    )
}

/// An `Integer` literal, negative ones as a negation of their magnitude.
fn integer_literal(text: &str) -> ContractExpression {
    match text.strip_prefix('-') {
        Some(magnitude) => ContractExpression::Negate(Box::new(
            ContractExpression::IntegerLiteral(magnitude.into()),
        )),
        None => ContractExpression::IntegerLiteral(text.into()),
    }
}

/// The sums and differences observed by `to_integer(...)` in `expression`.
fn observed_operations(expression: &ContractExpression, found: &mut Vec<ContractExpression>) {
    if let ContractExpression::Call { name, arguments } = expression
        && name == "to_integer"
        && let [argument] = arguments.as_slice()
        && matches!(
            argument,
            ContractExpression::Add(..) | ContractExpression::Subtract(..)
        )
        && !found.contains(argument)
    {
        found.push(argument.clone());
    }
    match expression {
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right) => {
            observed_operations(left, found);
            observed_operations(right, found);
        }
        ContractExpression::Negate(value) => observed_operations(value, found),
        ContractExpression::Call { arguments, .. } => {
            for argument in arguments {
                observed_operations(argument, found);
            }
        }
        _ => {}
    }
}

fn proposition_operations(proposition: &ClickProposition) -> Vec<ContractExpression> {
    let mut found = Vec::new();
    if let ClickProposition::Comparison { left, right, .. } = proposition {
        observed_operations(left, &mut found);
        observed_operations(right, &mut found);
    }
    found
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
        if !crate::kernel::proof::integer_arithmetic::written_integer_affine_claim(goal) {
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
        let mut carried = self.carried_machine_facts(&candidates);
        // Every sum or difference an `Integer` claim observes, from the
        // goal, the carried facts, and the connected `defined(...)` facts,
        // and every one nested inside an observed operation: each gets its
        // term-by-term observation and its type range.
        let mut operations = proposition_operations(surface_goal);
        for item in &carried {
            operations.extend(proposition_operations(&item.surface));
        }
        operations.extend(self.defined_operations(&candidates));
        let mut seen: Vec<ContractExpression> = Vec::new();
        while let Some(operation) = operations.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if seen.contains(&operation) {
                continue;
            }
            seen.push(operation.clone());
            let (left, right, subtract) = match &operation {
                ContractExpression::Add(left, right) => (left, right, false),
                ContractExpression::Subtract(left, right) => (left, right, true),
                _ => continue,
            };
            for operand in [left.as_ref(), right.as_ref()] {
                if matches!(
                    operand,
                    ContractExpression::Add(..) | ContractExpression::Subtract(..)
                ) {
                    operations.push(operand.clone());
                }
            }
            let exact = if subtract {
                ContractExpression::Subtract(
                    Box::new(to_integer(left)),
                    Box::new(to_integer(right)),
                )
            } else {
                ContractExpression::Add(Box::new(to_integer(left)), Box::new(to_integer(right)))
            };
            carried.push(Carried {
                surface: relate(to_integer(&operation), exact, Relation::Equal),
                establish: Establish::Operation {
                    left: left.as_ref().clone(),
                    right: right.as_ref().clone(),
                    subtract,
                    operation: operation.clone(),
                },
            });
            carried.extend(range_items(&operation));
        }
        if carried.is_empty() {
            return Ok(None);
        }

        // Lower candidate statements without constructing proofs for them.
        // Only a successful solver plan selects which bridge steps to issue.
        let planned = carried
            .iter()
            .filter_map(|item| {
                self.lower_cited_surface_proposition(&item.surface, "planned carried fact")
                    .ok()
                    .map(|kernel| (kernel, item))
            })
            .collect::<Vec<_>>();
        let mut rejected = BTreeSet::new();
        let mut established = BTreeSet::new();
        let mut proof = self.clone();
        loop {
            let mut premises = candidates.clone();
            premises.extend(
                planned
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| !rejected.contains(index))
                    .map(|(_, (kernel, _))| kernel.clone()),
            );
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
            // A proposed bridge can have an unproved prerequisite, such as
            // an unsigned operation's no-wrap bound. Remove that candidate
            // and try another plan, retaining every successful construction.
            let mut failed = None;
            for (index, (kernel, item)) in planned.iter().enumerate() {
                if rejected.contains(&index)
                    || established.contains(&index)
                    || !used.contains(kernel)
                {
                    continue;
                }
                if proof.facts().contains(kernel) {
                    established.insert(index);
                    continue;
                }
                match item.establish(&proof)? {
                    Some(next) => {
                        proof = next;
                        established.insert(index);
                    }
                    None => {
                        failed = Some(index);
                        break;
                    }
                }
            }
            if let Some(index) = failed {
                rejected.insert(index);
                continue;
            }
            // A cited fact with no source spelling leaves the certificate
            // unwritable, so the solver does not close the goal.
            let Some(pairs) =
                used.iter()
                    .map(|premise| {
                        match planned.iter().enumerate().find(|(index, (kernel, _))| {
                            !rejected.contains(index) && kernel == premise
                        }) {
                            Some((_, (_, item))) => Some((premise.clone(), item.surface.clone())),
                            None => proof
                                .resolve_simp_premises(std::slice::from_ref(premise), &[])
                                .and_then(|mut spelled| spelled.pop()),
                        }
                    })
                    .collect::<Option<Vec<_>>>()
            else {
                return Ok(None);
            };
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
    }

    /// The equality-by-bounds closure as `auto` tries it before `simp`. A
    /// plain 64-bit equality, with no sum or difference on either side,
    /// waits for `simp` and the wide-equality route after it: proving it by
    /// bounds here would run a nested `auto` for each bound ahead of them.
    pub(in crate::surface::proof) fn try_solver_equality_closure_before_simp(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        if let (
            Some(Proposition::ConditionIs(ConditionTerm::Bitvector64Equal(..), true)),
            Some(ClickProposition::Comparison { left, right, .. }),
        ) = (self.goal(), self.surface_goal())
            && !writes_sum_or_difference(left, right)
        {
            return Ok(None);
        }
        self.try_solver_equality_closure()
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
        // A plain 32-bit equality, with no sum or difference on either side,
        // already has the indexed native-reading solver route; proving it by
        // bounds would repeat that search for each bound.
        if let (
            Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(..), true),
            ClickProposition::Comparison { left, right, .. },
        ) = (goal, surface_goal)
            && !writes_sum_or_difference(left, right)
        {
            return Ok(None);
        }
        // A 64-bit equality has a reading in each signedness; either is an
        // Integer equality.
        if !crate::kernel::proof::integer_arithmetic::integer_affine_claims(goal)
            .iter()
            .any(|claim| {
                claim.relation
                    == crate::kernel::proof::integer_arithmetic::IntegerAffineRelation::Equal
            })
        {
            return Ok(None);
        }
        let _arithmetic_scope = matches!(
            goal,
            Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(..), true)
        )
        .then(MachineEqualityBridgeScope::enter);
        // A native equality is split as its observed reading, so a bound
        // such as `0u64 <= x` that holds by its type stays a stated Integer
        // fact rather than folding to `true`.
        let observed =
            super::smart_closures::observed_native_surface_comparison(goal, surface_goal);
        let ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right,
        } = &observed
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

    /// `auto` on a proposition goal with no C to run: the solver routes,
    /// then `simp`.
    pub(in crate::surface::proof) fn try_auto_proof_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        if let Some(closed) = self.try_single_rewrite_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_solver_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_bridged_solver_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_machine_goal_solver_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_solver_equality_closure_before_simp()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_definedness_solver_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_auto_conjunction_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_simp_closure()? {
            return Ok(Some(closed));
        }
        // Before the rewrite search: it costs little when it does not apply.
        if let Some(closed) = self.try_definition_condition_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_auto_equality_chain_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_constructor_join_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_wide_equality_solver_closure()? {
            return Ok(Some(closed));
        }
        self.try_native_goal_by_integer_reading()
    }

    /// A goal that restates an available fact through one connected
    /// equality, such as `f(Node(..)) == 1` beside `f(t) == 1` and
    /// `t == Node(..)`: one `rewrite` and `assumption`. Tried before the
    /// solvers, which would prove it too, at far greater cost and through a
    /// much longer certificate. At most `SINGLE_REWRITES` rewrites.
    pub(in crate::surface::proof) fn try_single_rewrite_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        use crate::kernel::proof::equality_rewrite::{equality_rewrite_applies, reverse_equality};
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        let Some(equalities) =
            crate::surface::planning::proposition_search::solver_connected_equalities(
                self.facts().assumptions(),
                goal,
            )
        else {
            return Ok(None);
        };
        let mut attempts = 0;
        for equality in &equalities {
            let applies = |kernel: &Proposition| {
                equality_rewrite_applies(goal, kernel)
                    || reverse_equality(kernel)
                        .is_some_and(|reverse| equality_rewrite_applies(goal, &reverse))
            };
            if !applies(equality) {
                continue;
            }
            check_verification_deadline()?;
            let Some((kernel, surface)) = self
                .resolve_simp_premises(std::slice::from_ref(equality), &[])
                .and_then(|mut spelled| spelled.pop())
            else {
                continue;
            };
            let mut forms = Vec::new();
            if let Some(unanchored) = unanchored_equality(&surface)
                && let Ok(lowered) =
                    self.lower_surface_proposition(&unanchored, "`auto` rewrite equality")
            {
                forms.extend(oriented_forms(lowered, unanchored));
            }
            forms.extend(oriented_forms(kernel, surface));
            for (kernel, surface) in forms {
                if !equality_rewrite_applies(goal, &kernel) {
                    continue;
                }
                if attempts == SINGLE_REWRITES {
                    return Ok(None);
                }
                attempts += 1;
                let Ok(rewritten) = self.apply_step(ProofStep::Rewrite(surface)) else {
                    continue;
                };
                if let Ok(closed) = rewritten.apply_step(ProofStep::Assumption)
                    && (closed.focused_discharged() || closed.is_complete())
                {
                    return Ok(Some(closed));
                }
            }
        }
        Ok(None)
    }

    /// Rewrite the goal by the equality facts connected to it until
    /// `assumption`, `normalize` or another direct closer finishes it: the
    /// congruence step `simp` takes only once its decider has selected the
    /// premises, here offered every connected equality, algebraic `==` facts
    /// included. Each rewrite is an ordinary checked step.
    pub(in crate::surface::proof) fn try_auto_equality_chain_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        use crate::kernel::proof::equality_rewrite::{equality_rewrite_applies, reverse_equality};
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        let Some(mut equalities) =
            crate::surface::planning::proposition_search::solver_connected_equalities(
                self.facts().assumptions(),
                goal,
            )
        else {
            return Ok(None);
        };
        // Equalities that rewrite the goal itself come first, so the
        // spelling cap keeps the ones a short chain starts from.
        let applies = |kernel: &Proposition| {
            equality_rewrite_applies(goal, kernel)
                || reverse_equality(kernel)
                    .is_some_and(|reverse| equality_rewrite_applies(goal, &reverse))
        };
        equalities.sort_by_key(|equality| !applies(equality));
        let mut candidates: Vec<Vec<(Proposition, ClickProposition)>> = Vec::new();
        for equality in &equalities {
            check_verification_deadline()?;
            if candidates.len() >= REWRITE_EQUALITIES {
                break;
            }
            let Some((kernel, surface)) = self
                .resolve_simp_premises(std::slice::from_ref(equality), &[])
                .and_then(|mut spelled| spelled.pop())
            else {
                continue;
            };
            // A fact recorded at a statement's entry is spelled there; its
            // unanchored form denotes the same fact where the proof stands
            // when nothing it names has changed since, which lowering and
            // the checked rewrite decide. Offer the unanchored form first.
            if let Some(unanchored) = unanchored_equality(&surface)
                && let Ok(lowered) =
                    self.lower_surface_proposition(&unanchored, "`auto` rewrite equality")
            {
                candidates.push(oriented_forms(lowered, unanchored));
            }
            candidates.push(oriented_forms(kernel, surface));
        }
        if candidates.is_empty() {
            return Ok(None);
        }
        let mut seen = std::collections::BTreeMap::from([(goal.clone(), REWRITE_DEPTH)]);
        let mut budget = RewriteBudget {
            attempts: REWRITE_ATTEMPTS,
            simp_closures: REWRITE_SIMP_CLOSURES,
        };
        self.rewrite_search(
            &candidates,
            &mut vec![false; candidates.len()],
            REWRITE_DEPTH,
            &mut seen,
            &mut budget,
        )
    }

    /// `auto` on a goal about the fields of a value that two connected facts
    /// equate to constructor applications, `t == Node(c, r)` and
    /// `t == Node(Black, Empty)`: it states `Node(c, r) == Node(Black, Empty)`,
    /// proved by rewriting each application to `t`, and `simp` then reads the
    /// fields' equalities (or the constructors' mismatch) from it. At most
    /// `CONSTRUCTOR_EQUATIONS` connected equations are paired.
    pub(in crate::surface::proof) fn try_constructor_join_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        let Some(equalities) =
            crate::surface::planning::proposition_search::solver_connected_equalities(
                self.facts().assumptions(),
                goal,
            )
        else {
            return Ok(None);
        };
        // Each equation as the value it names, its constructor application,
        // and the fact oriented `application == value`.
        let mut equations: Vec<(
            crate::kernel::AlgebraicTerm,
            ContractExpression,
            ClickProposition,
        )> = Vec::new();
        for equality in &equalities {
            check_verification_deadline()?;
            if equations.len() >= CONSTRUCTOR_EQUATIONS {
                break;
            }
            let Some((left, right)) = algebraic_sides(equality) else {
                continue;
            };
            let (left_built, right_built) = (is_constructor(left), is_constructor(right));
            if left_built == right_built {
                continue;
            }
            let Some((_, surface)) = self
                .resolve_simp_premises(std::slice::from_ref(equality), &[])
                .and_then(|mut spelled| spelled.pop())
            else {
                continue;
            };
            let ClickProposition::Comparison {
                left: written_left,
                operator: ComparisonOperator::Equal,
                right: written_right,
            } = surface
            else {
                continue;
            };
            let (value, application, value_written) = if left_built {
                (right, written_left, written_right)
            } else {
                (left, written_right, written_left)
            };
            let oriented = ClickProposition::Comparison {
                left: application.clone(),
                operator: ComparisonOperator::Equal,
                right: value_written,
            };
            equations.push((value.clone(), application, oriented));
        }
        for (index, (value, first, first_fact)) in equations.iter().enumerate() {
            for (other, second, second_fact) in &equations[index + 1..] {
                check_verification_deadline()?;
                if value != other || first == second {
                    continue;
                }
                let joined = ClickProposition::Comparison {
                    left: first.clone(),
                    operator: ComparisonOperator::Equal,
                    right: second.clone(),
                };
                let Ok(next) = self.apply_step(have(
                    joined,
                    vec![
                        ProofStep::Rewrite(first_fact.clone()),
                        ProofStep::Rewrite(second_fact.clone()),
                        ProofStep::Normalize,
                    ],
                )) else {
                    continue;
                };
                if next.is_complete() {
                    return Ok(Some(next));
                }
                if let Some(closed) = next.try_simp_closure()? {
                    return Ok(Some(closed));
                }
            }
        }
        Ok(None)
    }

    /// `auto` on a goal that is a condition inside a function's definition,
    /// given a fact `f(args) == k` whose arguments decide the definition's
    /// `match`es: `is_rb(left) == 1` from `is_rb(Node(.., left, right)) == 1`.
    /// Where every way through the definition's `if`s that does not take
    /// the goal's `then` arm ends in a constant other than `k`, the fact
    /// forces the goal. The proof is the one written by hand: `if` the goal
    /// holds, `assumption`; otherwise split on each condition met before the
    /// goal's, and at each end `have f(args) != k` by `unfold` and
    /// `normalize` using the conditions taken, then `contradiction`.
    pub(in crate::surface::proof) fn try_definition_condition_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        let (Some(goal), Some(surface_goal)) = (self.goal(), self.surface_goal()) else {
            return Ok(None);
        };
        let Some(equalities) =
            crate::surface::planning::proposition_search::solver_connected_equalities(
                self.facts().assumptions(),
                goal,
            )
        else {
            return Ok(None);
        };
        let functions = self.spec_functions();
        // Each fact as written, and the constructor each connected equation
        // names a value as, with that equation oriented `C(...) == value`.
        let mut spelled = Vec::new();
        let mut constructors: Vec<(ContractExpression, ContractExpression, ClickProposition)> =
            Vec::new();
        for equality in &equalities {
            check_verification_deadline()?;
            let Some((kernel, fact)) = self
                .resolve_simp_premises(std::slice::from_ref(equality), &[])
                .and_then(|mut spelled| spelled.pop())
            else {
                continue;
            };
            // A fact recorded at an earlier point is spelled there; its
            // unanchored form names the same fact when it lowers to it here.
            let fact = match unanchored_equality(&fact) {
                Some(unanchored)
                    if self
                        .lower_surface_proposition(&unanchored, "`auto` definition fact")
                        .is_ok_and(|lowered| lowered == kernel) =>
                {
                    unanchored
                }
                _ => fact,
            };
            if let ClickProposition::Comparison {
                left,
                operator: ComparisonOperator::Equal,
                right,
            } = &fact
            {
                let built = |side: &ContractExpression| {
                    matches!(side, ContractExpression::AlgebraicConstructor { .. })
                };
                if built(left) != built(right) && constructors.len() < CONSTRUCTOR_EQUATIONS {
                    let (application, value) = if built(left) {
                        (left, right)
                    } else {
                        (right, left)
                    };
                    constructors.push((
                        value.clone(),
                        application.clone(),
                        ClickProposition::Comparison {
                            left: application.clone(),
                            operator: ComparisonOperator::Equal,
                            right: value.clone(),
                        },
                    ));
                }
            }
            spelled.push(fact);
        }
        let goal_forms = DefinitionGoal {
            text: crate::surface::printing::source_click_proposition(surface_goal),
            surface: surface_goal,
            kernel: goal,
        };
        let mut tried = 0;
        for fact in &spelled {
            check_verification_deadline()?;
            let ClickProposition::Comparison {
                left,
                operator: ComparisonOperator::Equal,
                right,
            } = fact
            else {
                continue;
            };
            let (call, value_side, call_left) = match (left, right) {
                (ContractExpression::Call { .. }, value) => (left, value, true),
                (value, ContractExpression::Call { .. }) => (right, value, false),
                _ => continue,
            };
            let (ContractExpression::Call { name, arguments }, Some(value)) =
                (call, definition_end_value(value_side))
            else {
                continue;
            };
            let truth = crate::surface::bool_literal_value(value_side).is_some();
            let Some(definition) = functions.get(name) else {
                continue;
            };
            if definition.parameters().len() != arguments.len() {
                continue;
            }
            if tried == DEFINITION_FACTS {
                break;
            }
            tried += 1;
            // The fact as written, and the fact with each argument a connected
            // equation names as a constructor replaced by it, stated by
            // rewriting it back: `match` arms over the argument are decided
            // only in the second.
            let mut readings = vec![(arguments.clone(), fact.clone(), None)];
            let mut rewrites = Vec::new();
            let restated = arguments
                .iter()
                .map(
                    |argument| match constructors.iter().find(|(value, _, _)| value == argument) {
                        Some((_, application, equation)) => {
                            rewrites.push(ProofStep::Rewrite(equation.clone()));
                            application.clone()
                        }
                        None => argument.clone(),
                    },
                )
                .collect::<Vec<_>>();
            if !rewrites.is_empty() {
                let restated_call = ContractExpression::Call {
                    name: name.clone(),
                    arguments: restated.clone(),
                };
                let restated_fact = ClickProposition::Comparison {
                    left: if call_left {
                        restated_call.clone()
                    } else {
                        left.clone()
                    },
                    operator: ComparisonOperator::Equal,
                    right: if call_left {
                        right.clone()
                    } else {
                        restated_call
                    },
                };
                rewrites.push(ProofStep::Assumption);
                readings.push((restated, restated_fact, Some(rewrites)));
            }
            for (arguments, fact, restatement) in readings {
                // Plan first: it reads only the definition, so a fact whose
                // definition never reaches the goal costs no checked step.
                let environment = definition
                    .parameters()
                    .iter()
                    .zip(&arguments)
                    .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
                    .collect::<BTreeMap<_, _>>();
                let mut leaves = 0;
                let mut meets_goal = false;
                let Some(plan) = self.definition_condition_plan(
                    definition.body(),
                    &environment,
                    &goal_forms,
                    value,
                    &mut leaves,
                    &mut meets_goal,
                    &[],
                ) else {
                    continue;
                };
                if !meets_goal {
                    continue;
                }
                let base = match restatement {
                    None => self.clone(),
                    Some(steps) => match self.apply_step(have(fact.clone(), steps)) {
                        Ok(base) => base,
                        Err(_) => continue,
                    },
                };
                if let Some(closed) = base.read_definition_condition(
                    &plan,
                    surface_goal,
                    name,
                    &arguments,
                    fact,
                    call_left,
                    truth,
                )? {
                    return Ok(Some(closed));
                }
            }
        }
        Ok(None)
    }

    /// The specification functions in scope for this proof.
    fn spec_functions(&self) -> &'a ClickFunctionEnvironment {
        match self.context.as_ref() {
            ProofContext::Pure(context) => context.spec_definitions.functions,
            ProofContext::FixedState(context) => context.spec_definitions.functions,
            ProofContext::Execution(context) => context.spec_definitions.functions,
        }
    }

    /// Closes the goal from one fact `f(arguments) == value` along `plan`,
    /// as [`Self::try_definition_condition_closure`] describes.
    fn read_definition_condition(
        &self,
        plan: &DefinitionPlan,
        surface_goal: &ClickProposition,
        name: &str,
        arguments: &[ContractExpression],
        fact: ClickProposition,
        call_left: bool,
        truth: bool,
    ) -> Result<Option<Self>, ClickError> {
        let ClickProposition::Comparison { left, right, .. } = &fact else {
            return Ok(None);
        };
        let call = if call_left { left } else { right };
        let refutation = DefinitionRefutation {
            application: ClickFunctionApplication {
                name: name.to_string(),
                arguments: arguments.to_vec(),
            },
            // A `bool` fact is refuted by its negation, which lowers to the
            // exact opposite polarity `contradiction` reads.
            differs: if truth {
                ClickProposition::Not(Box::new(fact.clone()))
            } else {
                ClickProposition::Comparison {
                    left: if call_left {
                        call.clone()
                    } else {
                        left.clone()
                    },
                    operator: ComparisonOperator::NotEqual,
                    right: if call_left {
                        right.clone()
                    } else {
                        call.clone()
                    },
                }
            },
            fact: fact.clone(),
            negated_goal: ClickProposition::Not(Box::new(surface_goal.clone())),
        };
        let Ok((split_proof, split, ids)) = self.split_focused_if(surface_goal.clone()) else {
            return Ok(None);
        };
        let marker = split_proof.checkpoint();
        let Some(then_done) = split_proof
            .focus_branch(ids[0])
            .and_then(|branch| branch.apply_step(ProofStep::Assumption))
            .ok()
            .filter(Proof::focused_discharged)
        else {
            return Ok(None);
        };
        let Ok(else_branch) = then_done.focus_branch(ids[1]) else {
            return Ok(None);
        };
        let Some(else_done) = else_branch.refute_definition_ends(plan, &refutation, &[])? else {
            return Ok(None);
        };
        Ok(else_done
            .join_focused_if(&marker, split, ids, surface_goal.clone())
            .ok())
    }

    /// The conditional tree of a definition body under `environment`, cut
    /// at the goal's own condition, whose `else` arm alone is followed. A
    /// `match` must meet a constructor; an end that applies a defined
    /// function is followed into that definition, at most
    /// `DEFINITION_UNFOLDS` deep, and each end that remains must be an
    /// integer or `bool` constant other than `value`. `unfolds` are the
    /// applications already followed to reach `body`. `None` when any of
    /// that fails or the tree has more than `DEFINITION_LEAVES` ends.
    #[allow(clippy::too_many_arguments)]
    fn definition_condition_plan(
        &self,
        body: &ContractExpression,
        environment: &BTreeMap<String, ContractExpression>,
        goal: &DefinitionGoal<'_>,
        value: i128,
        leaves: &mut usize,
        meets_goal: &mut bool,
        unfolds: &[ClickFunctionApplication],
    ) -> Option<DefinitionPlan> {
        match body {
            ContractExpression::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let condition = substitute_click_proposition(condition, environment).ok()?;
                // Compared as written first; a condition spelled otherwise,
                // as `v == x` against a postcondition's `result == x`, is
                // lowered only when its shape is the goal's. The checked
                // steps decide whether the condition is the goal.
                if crate::surface::printing::source_click_proposition(&condition) == goal.text
                    || (same_shape(&condition, goal.surface)
                        && self
                            .lower_surface_proposition(&condition, "`auto` definition condition")
                            .is_ok_and(|lowered| lowered == *goal.kernel))
                {
                    *meets_goal = true;
                    return self.definition_condition_plan(
                        else_branch,
                        environment,
                        goal,
                        value,
                        leaves,
                        meets_goal,
                        unfolds,
                    );
                }
                let then_plan = self.definition_condition_plan(
                    then_branch,
                    environment,
                    goal,
                    value,
                    leaves,
                    meets_goal,
                    unfolds,
                )?;
                let else_plan = self.definition_condition_plan(
                    else_branch,
                    environment,
                    goal,
                    value,
                    leaves,
                    meets_goal,
                    unfolds,
                )?;
                Some(DefinitionPlan::Split {
                    condition,
                    then_plan: Box::new(then_plan),
                    else_plan: Box::new(else_plan),
                })
            }
            ContractExpression::AlgebraicMatch { scrutinee, arms } => {
                let ContractExpression::AlgebraicConstructor {
                    variant, arguments, ..
                } = substitute_contract_expression(scrutinee, environment).ok()?
                else {
                    return None;
                };
                let arm = arms.iter().find(|arm| arm.variant == variant)?;
                if arm.bindings.len() != arguments.len() {
                    return None;
                }
                let mut environment = environment.clone();
                environment.extend(arm.bindings.iter().cloned().zip(arguments));
                self.definition_condition_plan(
                    &arm.body,
                    &environment,
                    goal,
                    value,
                    leaves,
                    meets_goal,
                    unfolds,
                )
            }
            ContractExpression::Call { name, arguments } if unfolds.len() < DEFINITION_UNFOLDS => {
                let definition = self.spec_functions().get(name)?;
                if definition.parameters().len() != arguments.len() {
                    return None;
                }
                let arguments = arguments
                    .iter()
                    .map(|argument| substitute_contract_expression(argument, environment).ok())
                    .collect::<Option<Vec<_>>>()?;
                let inner = definition
                    .parameters()
                    .iter()
                    .zip(&arguments)
                    .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
                    .collect::<BTreeMap<_, _>>();
                let mut unfolds = unfolds.to_vec();
                unfolds.push(ClickFunctionApplication {
                    name: name.clone(),
                    arguments,
                });
                self.definition_condition_plan(
                    definition.body(),
                    &inner,
                    goal,
                    value,
                    leaves,
                    meets_goal,
                    &unfolds,
                )
            }
            end => {
                *leaves += 1;
                (*leaves <= DEFINITION_LEAVES
                    && definition_end_value(end).is_some_and(|end| end != value))
                .then(|| DefinitionPlan::End {
                    unfolds: unfolds.to_vec(),
                })
            }
        }
    }

    /// Closes the focused branch, where the goal is false, along `plan`:
    /// each split is a proof `if`, and each end refutes the fact.
    fn refute_definition_ends(
        &self,
        plan: &DefinitionPlan,
        refutation: &DefinitionRefutation,
        taken: &[ClickProposition],
    ) -> Result<Option<Self>, ClickError> {
        check_verification_deadline()?;
        match plan {
            DefinitionPlan::End { unfolds } => {
                let mut using = taken.to_vec();
                using.push(refutation.negated_goal.clone());
                let mut steps = vec![ProofStep::UnfoldFunction(refutation.application.clone())];
                steps.extend(unfolds.iter().cloned().map(ProofStep::UnfoldFunction));
                steps.push(ProofStep::NormalizeUsing(using));
                let refuted = self
                    .apply_step(have(refutation.differs.clone(), steps))
                    .and_then(|next| {
                        next.apply_step(ProofStep::Contradiction(refutation.fact.clone()))
                    });
                Ok(refuted.ok().filter(Proof::focused_discharged))
            }
            DefinitionPlan::Split {
                condition,
                then_plan,
                else_plan,
            } => {
                let Ok((split_proof, split, ids)) = self.split_focused_if(condition.clone()) else {
                    return Ok(None);
                };
                let marker = split_proof.checkpoint();
                let mut then_taken = taken.to_vec();
                then_taken.push(condition.clone());
                let Ok(then_branch) = split_proof.focus_branch(ids[0]) else {
                    return Ok(None);
                };
                let Some(then_done) =
                    then_branch.refute_definition_ends(then_plan, refutation, &then_taken)?
                else {
                    return Ok(None);
                };
                let mut else_taken = taken.to_vec();
                else_taken.push(ClickProposition::Not(Box::new(condition.clone())));
                let Ok(else_branch) = then_done.focus_branch(ids[1]) else {
                    return Ok(None);
                };
                let Some(else_done) =
                    else_branch.refute_definition_ends(else_plan, refutation, &else_taken)?
                else {
                    return Ok(None);
                };
                Ok(else_done
                    .join_focused_if(&marker, split, ids, condition.clone())
                    .ok())
            }
        }
    }

    /// A bounded depth-first search over rewrite sequences: every applicable
    /// equality in either direction, each used at most once, closing after
    /// every step by `assumption`, `normalize` or the direct logical closer.
    /// An orientation whose left side does not occur in the goal costs no
    /// checked step. A goal already reached with at least as many rewrites
    /// left is not explored again, and the whole search tries at most
    /// `REWRITE_ATTEMPTS` rewrites.
    fn rewrite_search(
        &self,
        candidates: &[Vec<(Proposition, ClickProposition)>],
        used: &mut Vec<bool>,
        depth: usize,
        seen: &mut std::collections::BTreeMap<Proposition, usize>,
        budget: &mut RewriteBudget,
    ) -> Result<Option<Self>, ClickError> {
        let Some(current) = self.goal() else {
            return Ok(None);
        };
        for (index, forms) in candidates.iter().enumerate() {
            if used[index] {
                continue;
            }
            for (kernel, surface) in forms {
                check_verification_deadline()?;
                if !crate::kernel::proof::equality_rewrite::equality_rewrite_applies(
                    current, kernel,
                ) {
                    continue;
                }
                if budget.attempts == 0 {
                    return Ok(None);
                }
                budget.attempts -= 1;
                let Ok(rewritten) = self.apply_step(ProofStep::Rewrite(surface.clone())) else {
                    continue;
                };
                let Some(goal) = rewritten.goal().cloned() else {
                    continue;
                };
                let left = depth - 1;
                match seen.get(&goal) {
                    Some(&reached) if reached >= left => continue,
                    Some(_) => {}
                    None => {
                        if let Some(closed) = rewritten.try_close_after_rewrite(budget)? {
                            return Ok(Some(closed));
                        }
                    }
                }
                seen.insert(goal, left);
                if depth > 1 {
                    used[index] = true;
                    let found =
                        rewritten.rewrite_search(candidates, used, depth - 1, seen, budget)?;
                    used[index] = false;
                    if found.is_some() {
                        return Ok(found);
                    }
                }
            }
        }
        Ok(None)
    }

    fn try_close_after_rewrite(
        &self,
        budget: &mut RewriteBudget,
    ) -> Result<Option<Self>, ClickError> {
        // Inside a `have`, the stated fact is the focused goal; the proof
        // around it is not complete yet.
        let closes = |proof: &Self| proof.focused_discharged() || proof.is_complete();
        if let Ok(closed) = self.apply_step(ProofStep::Assumption)
            && closes(&closed)
        {
            return Ok(Some(closed));
        }
        if let Ok(closed) = self.apply_step(ProofStep::Normalize)
            && closes(&closed)
        {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_direct_logical_closure().ok().flatten() {
            return Ok(Some(closed));
        }
        if budget.simp_closures == 0 {
            return Ok(None);
        }
        budget.simp_closures -= 1;
        Ok(self.try_simp_closure()?.filter(closes))
    }

    /// A conjunction goal: each conjunct by `auto` on the stated fact, then
    /// `assumption`, which closes a conjunction whose sides are facts.
    pub(in crate::surface::proof) fn try_auto_conjunction_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        let Some(ClickProposition::And(left, right)) = self.surface_goal() else {
            return Ok(None);
        };
        let Some(proof) = self.prove_stated_fact(left)? else {
            return Ok(None);
        };
        let Some(proof) = proof.prove_stated_fact(right)? else {
            return Ok(None);
        };
        attempt::candidate_outcome(proof.apply_step(ProofStep::Assumption))
    }

    /// Prove `fact` where the proof stands with `auto` on the stated fact,
    /// as `have fact by auto();` does.
    fn prove_stated_fact(&self, fact: &ClickProposition) -> Result<Option<Self>, ClickError> {
        let Ok(scope) = self.begin_have(fact.clone()) else {
            return Ok(None);
        };
        let Some(closed) = scope.try_auto_fact_closure()? else {
            return Ok(None);
        };
        Ok(closed.join().ok())
    }

    /// Close `defined(a + b)` or `defined(a - b)` over `int32` or `int64`:
    /// prove both `Integer` bounds of the exact result with `auto`, then
    /// apply the type's `..._defined_by_integer_bounds` theorem.
    pub(in crate::surface::proof) fn try_definedness_solver_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        let Some(ClickProposition::Defined { expression }) = self.surface_goal() else {
            return Ok(None);
        };
        let (left, right, subtract) = match expression {
            ContractExpression::Add(left, right) => (left, right, false),
            ContractExpression::Subtract(left, right) => (left, right, true),
            _ => return Ok(None),
        };
        let exact = if subtract {
            ContractExpression::Subtract(Box::new(to_integer(left)), Box::new(to_integer(right)))
        } else {
            ContractExpression::Add(Box::new(to_integer(left)), Box::new(to_integer(right)))
        };
        let stem = if subtract { "subtract" } else { "add" };
        // An operand that is itself an operation must be defined too; prove
        // that first so the outer theorem's conclusion completes the goal.
        let mut base = self.clone();
        for operand in [left.as_ref(), right.as_ref()] {
            if matches!(
                operand,
                ContractExpression::Add(..) | ContractExpression::Subtract(..)
            ) {
                let defined = ClickProposition::Defined {
                    expression: operand.clone(),
                };
                if let Some(next) = base.prove_stated_fact(&defined)? {
                    base = next;
                }
            }
        }
        for (width, minimum, maximum) in [
            ("int32", "-2147483648", "2147483647"),
            ("int64", "-9223372036854775808", "9223372036854775807"),
        ] {
            let lower = ClickProposition::Comparison {
                left: exact.clone(),
                operator: ComparisonOperator::GreaterEqual,
                right: ContractExpression::IntegerLiteral(minimum.into()),
            };
            let upper = relate(
                exact.clone(),
                ContractExpression::IntegerLiteral(maximum.into()),
                Relation::LessEqual,
            );
            let Some(bounded) = base.prove_stated_fact(&lower)? else {
                continue;
            };
            let Some(bounded) = bounded.prove_stated_fact(&upper)? else {
                continue;
            };
            let Ok(applied) = bounded.apply_step(apply(
                &format!("{width}_{stem}_defined_by_integer_bounds"),
                vec![left.as_ref().clone(), right.as_ref().clone()],
                vec![lower, upper],
            )) else {
                continue;
            };
            if applied.is_complete() || applied.goal() != self.goal() {
                return Ok(Some(applied));
            }
            // The goal may also ask that each operand is defined, which
            // the facts already say.
            if let Some(closed) = applied.try_direct_logical_closure().ok().flatten() {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    /// Close a machine order goal `a < b` or `a <= b` by proving its
    /// `Integer` reading with `auto` on the stated fact and carrying it back
    /// with the type's bridge (`uint64_to_integer_less_than_implies_less_than`,
    /// ...). Any miss leaves the proof unchanged.
    pub(in crate::surface::proof) fn try_machine_goal_solver_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        self.try_machine_goal_solver_closure_for(false)
    }

    /// `try_machine_goal_solver_closure` for a 64-bit equality goal. Its
    /// `Integer` reading is proved before the type is known, so it costs
    /// more than the other machine goals; `auto` tries it last, after
    /// `simp` and its rewrite search.
    pub(in crate::surface::proof) fn try_wide_equality_solver_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        self.try_machine_goal_solver_closure_for(true)
    }

    fn try_machine_goal_solver_closure_for(
        &self,
        wide_equality: bool,
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
        if (order == MachineOrder::Equal64) != wide_equality {
            return Ok(None);
        }
        let Some((lower, upper, relation, true)) = relation_parts(surface_goal) else {
            return Ok(None);
        };
        let _arithmetic_scope = matches!(
            goal,
            Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(..), true)
        )
        .then(MachineEqualityBridgeScope::enter);
        // A machine comparison is the Integer comparison of its operands'
        // exact observations, so its Integer reading is the goal itself:
        // state each sum or difference defined, as `to_integer` of it needs,
        // and close the goal by the Integer solver with operation identities.
        let _ = order;
        let mut base = self.clone();
        let mut stated = false;
        for side in [&lower, &upper] {
            if matches!(
                side,
                ContractExpression::Add(..) | ContractExpression::Subtract(..)
            ) {
                let defined = ClickProposition::Defined {
                    expression: side.clone(),
                };
                if let Some(next) = base.prove_stated_fact(&defined)? {
                    base = next;
                    stated = true;
                }
            }
        }
        // Without a stated definedness fact this is the solver run `auto`
        // already made on the goal. Plain 32-bit equality, with no sum or
        // difference to observe, already has the indexed native-reading
        // solver route; re-entering it by bounds repeats equality-by-bounds
        // and snapshot search for the same comparison.
        if !stated && !wide_equality {
            return Ok(None);
        }
        // The solver refutes bounds; an equality is proved from its two.
        if relation == Relation::Equal {
            return base.try_solver_equality_closure();
        }
        base.solver_closure(true, &[])
    }

    /// The sums and differences named by connected `defined(...)` facts.
    fn defined_operations(&self, candidates: &[Proposition]) -> Vec<ContractExpression> {
        let mut operations = Vec::new();
        for candidate in candidates {
            if !matches!(
                candidate,
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedAddOverflows(..)
                        | ConditionTerm::Bitvector32SignedSubtractOverflows(..)
                        | ConditionTerm::Bitvector64SignedAddOverflows(..)
                        | ConditionTerm::Bitvector64SignedSubtractOverflows(..),
                    false
                )
            ) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            if let Some((_, ClickProposition::Defined { expression })) = self
                .resolve_simp_premises(std::slice::from_ref(candidate), &[])
                .and_then(|mut spelled| spelled.pop())
                && matches!(
                    expression,
                    ContractExpression::Add(..) | ContractExpression::Subtract(..)
                )
            {
                operations.push(expression);
            }
        }
        operations
    }

    /// The `Integer` reading of each connected machine order fact, and the
    /// type range of each unsigned value they mention.
    fn carried_machine_facts(&self, candidates: &[Proposition]) -> Vec<Carried> {
        let mut carried = Vec::new();
        let mut ranged: Vec<ContractExpression> = Vec::new();
        for candidate in candidates {
            // A 64-bit equality is not carried: rewriting by it serves an
            // `Integer` claim without reading both types' ranges into every
            // solver call.
            let Some(order) =
                MachineOrder::of(candidate).filter(|order| *order != MachineOrder::Equal64)
            else {
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
            let carry = match relation {
                Relation::Less => vec![apply(
                    &format!("{}_less_than_to_integer", order.name()),
                    vec![lower.clone(), upper.clone()],
                    vec![stated],
                )],
                Relation::LessEqual => vec![apply(
                    &format!("{}_less_equal_to_integer", order.name()),
                    vec![lower.clone(), upper.clone()],
                    vec![stated],
                )],
                // Equal values have equal observations: rewriting by the
                // fact leaves an identity.
                Relation::Equal => vec![ProofStep::Rewrite(stated), ProofStep::Normalize],
            };
            steps.push(have(observed.clone(), carry));
            carried.push(Carried {
                establish: Establish::Steps(steps),
                surface: observed,
            });
            if let Some((theorem, minimum, maximum)) = order.range() {
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
                            integer_literal(minimum),
                            to_integer(&value),
                            Relation::LessEqual,
                        ),
                        relate(
                            to_integer(&value),
                            integer_literal(maximum),
                            Relation::LessEqual,
                        ),
                    ] {
                        carried.push(Carried {
                            establish: Establish::Steps(vec![have(
                                bound.clone(),
                                vec![bounds.clone()],
                            )]),
                            surface: bound,
                        });
                    }
                }
            }
        }
        carried
    }
}

/// The proof `if`s `auto` writes through a definition, and their ends.
enum DefinitionPlan {
    Split {
        condition: ClickProposition,
        then_plan: Box<DefinitionPlan>,
        else_plan: Box<DefinitionPlan>,
    },
    /// An end, reached through `unfolds`: the applications of the ends
    /// followed into their definitions, each unfolded after the fact's own.
    End {
        unfolds: Vec<ClickFunctionApplication>,
    },
}

/// What each end of a [`DefinitionPlan`] refutes: the fact `f(args) == k`,
/// by `f(args) != k` read from the definition with the goal false.
/// The goal a definition's conditions are compared with: as written, and
/// as lowered here.
struct DefinitionGoal<'g> {
    text: String,
    surface: &'g ClickProposition,
    kernel: &'g Proposition,
}

/// Whether two propositions are comparisons with the same operator, or
/// otherwise of the same kind: a lowered comparison is tried only then.
fn same_shape(left: &ClickProposition, right: &ClickProposition) -> bool {
    match (left, right) {
        (
            ClickProposition::Comparison { operator: left, .. },
            ClickProposition::Comparison {
                operator: right, ..
            },
        ) => left == right,
        _ => std::mem::discriminant(left) == std::mem::discriminant(right),
    }
}

struct DefinitionRefutation {
    application: ClickFunctionApplication,
    differs: ClickProposition,
    fact: ClickProposition,
    negated_goal: ClickProposition,
}

/// An integer constant, or a `bool` one as `1` or `0`: a definition's end
/// and the value a fact gives its application.
fn definition_end_value(expression: &ContractExpression) -> Option<i128> {
    integer_literal_value(expression)
        .or_else(|| crate::surface::bool_literal_value(expression).map(i128::from))
}

fn integer_literal_value(expression: &ContractExpression) -> Option<i128> {
    match expression {
        ContractExpression::IntegerLiteral(text) => text.parse().ok(),
        _ => None,
    }
}

/// Whether either side of a written comparison is a sum or a difference.
fn writes_sum_or_difference(left: &ContractExpression, right: &ContractExpression) -> bool {
    [left, right].into_iter().any(|side| {
        matches!(
            side,
            ContractExpression::Add(..) | ContractExpression::Subtract(..)
        )
    })
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/surface/proof/solver_bridges.rs");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `auto` reaches `simp` before splitting a plain 64-bit equality into
    /// its two bounds, each of which would run a nested `auto`.
    #[test]
    fn auto_leaves_a_plain_64_bit_equality_to_simp() {
        let source = r#"spec enum Color { Red, Black, }
function color_bit(color: Color) -> int32 {
    match color { Color::Red => 0, Color::Black => 1, }
}
theorem low_bit_is_the_color_bit(bits: uint64, color: Color) {
    requires (bits & 1u64) == (uint64)color_bit(color);
    ensures (bits & 1u64) == (uint64)color_bit(color) by {
        have (bits & 1u64) == (uint64)color_bit(color) by auto();
        assumption();
    }
}
"#;
        crate::surface::verify_click_theorems(source).unwrap();
        let line = source
            .lines()
            .position(|line| line.contains("by auto()"))
            .unwrap();
        let column = source.lines().nth(line).unwrap().find("auto()").unwrap();
        let expanded =
            crate::surface::expand_c0_tactic_source_at(source, &[], line + 1, column + 1).unwrap();
        assert!(!expanded.contains("equal_from_bounds"), "{expanded}");
        crate::surface::verify_click_theorems(&expanded).unwrap();
    }

    #[test]
    fn native_function_equalities_keep_contradiction_proofs_complete() {
        crate::surface::verify_click_theorems(
            r#"spec enum Color { Red, Black, }
function color_black(color: Color) -> int32 {
    match color { Color::Red => 0, Color::Black => 1, }
}
theorem black_color_is_black(color: Color) {
    requires color_black(color) == 1;
    ensures color == Color::Black by {
        induct(color) as ih {
            Color::Red => {
                have not(color_black(Color::Red) == 1) by auto();
                contradiction(color_black(Color::Red) == 1);
            }
            Color::Black => { normalize(); }
        }
    }
}
"#,
        )
        .unwrap();
    }

    #[test]
    fn native_rewrite_operands_survive_integer_source_expansion() {
        let used = Bitvector32Term::Variable(Variable(920_001));
        let capacity = Bitvector32Term::Variable(Variable(920_002));
        let slots = Bitvector32Term::Variable(Variable(920_003));
        let kernel = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(capacity),
                Box::new(Bitvector32Term::Add(Box::new(used), Box::new(slots))),
            ),
            true,
        );
        let name = |name: &str| ContractExpression::CFragment(CExpression::Variable(name.into()));
        let surface = ClickProposition::Comparison {
            left: name("capacity"),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::Add(Box::new(name("used")), Box::new(name("slots"))),
        };
        let forms = oriented_forms(kernel, surface);
        assert_eq!(forms.len(), 2);
        let equality = crate::surface::printing::source_click_proposition(&forms[0].1);
        let source = format!(
            r#"
            arithmetic "integer";
            theorem zero_remainder(used: int32, capacity: int32, slots: int32) {{
                requires defined(used + slots);
                requires defined(slots - capacity);
                requires to_integer(capacity) == to_integer(used) + to_integer(slots);
                requires used == 0;
                ensures to_integer(slots - capacity) == 0 by {{
                    have to_integer(slots - capacity) == 0 by {{
                        rewrite({equality});
                        rewrite(used == 0);
                        normalize();
                    }}
                    assumption();
                }}
            }}
        "#
        );
        crate::surface::verify_click_theorems(&source).unwrap();
    }
}
