//! `auto` on an `Integer` fact whose atoms observe machine values.
//!
//! Selected-premise arithmetic reads linear `Integer` claims. A proof about `to_integer(i)`
//! usually also needs what the program knows about `i` itself: `i < n` for
//! two `uint64` values says `to_integer(i) < to_integer(n)`, and a `uint64`
//! is never negative. Those facts reach that arithmetic as the steps a proof would
//! write by hand: each connected machine order fact is carried to `Integer`
//! by `assumption` (a comparison of observations is the native comparison),
//! and each unsigned value's observation gets its type range by an explicit
//! `type_range` certificate.
//! It then runs over the original and the carried facts, and only
//! the carried facts its certificate cites are kept, so the expansion holds
//! the bridges the proof needs and no others. Every step is an explicit
//! arithmetic certificate or `assumption`; nothing here is trusted.

use super::wide_arithmetic::{
    Carrier, Relation, have, operation_identity, relate, relation_parts, to_integer, type_range,
};
use super::*;
#[cfg(test)]
use crate::kernel::binary_node;
use crate::kernel::{CompareRelation, OverflowOperation};
use crate::surface::checking::{IntegerRefutation, refute_integer_goal};

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

/// How many rewrites `solve`'s connected-equality chain takes before closing.
const REWRITE_DEPTH: usize = 3;

/// How many connected equalities the search offers, and how many checked
/// rewrites it tries in all. A large connected component fails promptly
/// instead of exploring every short chain of its equalities.
const REWRITE_EQUALITIES: usize = 64;
const REWRITE_ATTEMPTS: usize = 256;

/// How many rewritten goals the search offers to `solve`, after the cheap
/// closers miss: `solve` unfolds and computes what a rewrite exposes.
const REWRITE_SOLVE_CLOSURES: usize = 8;

/// How many rewrites `solve`'s single-rewrite strategy tries, each followed
/// by `assumption`: a goal that restates a fact through one equation.
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

/// The machine type an order fact compares.
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
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    ..
                }
                | ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    ..
                }
                | ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterThan,
                    ..
                }
                | ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterEqual,
                    ..
                },
                _,
            ) => Some(Self::Int32),
            // An `int32` equality; a `uint32` one is refused by the `int32`
            // bridges and left out.
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal,
                    ..
                },
                true,
            ) => Some(Self::Int32),
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    ..
                },
                true,
            ) => Some(Self::Equal64),
            _ => None,
        }
    }

    fn typed_literals(self, expression: &ContractExpression) -> ContractExpression {
        match self {
            Self::Int32 | Self::Equal64 => expression.clone(),
            Self::Wide(carrier) => carrier.typed_literals(expression),
        }
    }

    /// The type range of a value's observation, as Integer literals, for
    /// the types a carried order reads ranges of.
    fn range(self) -> Option<(String, String)> {
        let ty = match self {
            Self::Int32 => crate::kernel::MachineIntegerType::Int32,
            Self::Wide(carrier) => carrier.machine_type(),
            Self::Equal64 => return None,
        };
        let (minimum, maximum) = crate::kernel::machine_integer::range::range(ty);
        Some((minimum.to_string(), maximum.to_string()))
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
        /// The operation's machine format.
        format: crate::kernel::MachineIntegerFormat,
    },
}

/// The format of the machine `+` or `-` whose observation an identity
/// `to_integer(a op b) == to_integer(a) op to_integer(b)` states.
fn observed_operation_format(
    identity: &Proposition,
) -> Option<crate::kernel::MachineIntegerFormat> {
    let Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true) = identity else {
        return None;
    };
    [left, right].into_iter().find_map(|side| {
        crate::kernel::machine_integer::identity::additive_mathematical(side)
            .map(|(ty, _)| ty.format())
    })
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
                format,
            } => {
                let exact = if *subtract {
                    ContractExpression::Subtract(
                        Box::new(to_integer(left)),
                        Box::new(to_integer(right)),
                    )
                } else {
                    ContractExpression::Add(Box::new(to_integer(left)), Box::new(to_integer(right)))
                };
                let (minimum, maximum) = format.bounds();
                let (minimum, maximum) = (minimum.to_string(), maximum.to_string());
                let (lower, upper) = (
                    relate(
                        integer_literal(&minimum),
                        exact.clone(),
                        Relation::LessEqual,
                    ),
                    relate(
                        exact.clone(),
                        integer_literal(&maximum),
                        Relation::LessEqual,
                    ),
                );
                // The identity, once both constant bounds of the exact value
                // are facts.
                let observe = |proof: &Proof<'a>| {
                    proof
                        .apply_step(have(
                            self.surface.clone(),
                            vec![operation_identity(
                                lower.clone(),
                                upper.clone(),
                                self.surface.clone(),
                            )],
                        ))
                        .ok()
                };
                if format.is_signed() {
                    // Definedness already is the pair of ordinary bounds.
                    // Cite each bound with the ordinary conjunction/assumption
                    // rule before checking the mathematical observation.
                    let bounded =
                        [&lower, &upper]
                            .into_iter()
                            .try_fold(proof.clone(), |proof, bound| {
                                proof
                                    .apply_step(have(bound.clone(), vec![ProofStep::Assumption]))
                                    .ok()
                            });
                    if let Some(observed) = bounded.as_ref().and_then(observe) {
                        return Ok(Some(observed));
                    }
                    let Some(_operation_scope) = OperationBridgeScope::enter(operation) else {
                        return Ok(None);
                    };
                    // Not yet known to be defined: prove both Integer bounds
                    // of the exact value, which together are its
                    // definedness, then observe. Each operand's type range,
                    // which the far bound of the exact value usually rests
                    // on, is stated first.
                    let mut ranged = proof.clone();
                    for operand in [left, right] {
                        if matches!(to_integer(operand), ContractExpression::IntegerLiteral(_)) {
                            continue;
                        }
                        for bound in [
                            relate(
                                integer_literal(&minimum),
                                to_integer(operand),
                                Relation::LessEqual,
                            ),
                            relate(
                                to_integer(operand),
                                integer_literal(&maximum),
                                Relation::LessEqual,
                            ),
                        ] {
                            if let Ok(next) =
                                ranged.apply_step(have(bound.clone(), vec![type_range(bound)]))
                            {
                                ranged = next;
                            }
                        }
                    }
                    let Some(next) = ranged.prove_stated_fact(&lower)? else {
                        return Ok(None);
                    };
                    let Some(next) = next.prove_stated_fact(&upper)? else {
                        return Ok(None);
                    };
                    return Ok(observe(&next));
                }
                // An unsigned operation that does not wrap: a sum at most
                // the type's maximum, a difference whose subtrahend is at
                // most its minuend.
                let guard = if *subtract {
                    relate(to_integer(right), to_integer(left), Relation::LessEqual)
                } else {
                    upper.clone()
                };
                let unsigned = |proof: &Proof<'a>| -> Result<Option<Proof<'a>>, ClickError> {
                    let Some(bounded) = proof.prove_stated_fact(&lower)? else {
                        return Ok(None);
                    };
                    let Some(bounded) = bounded.prove_stated_fact(&upper)? else {
                        return Ok(None);
                    };
                    Ok(observe(&bounded))
                };
                let Some(_operation_scope) = OperationBridgeScope::enter(operation) else {
                    return Ok(None);
                };
                if let Ok(next) = proof.apply_step(have(guard.clone(), vec![ProofStep::Assumption]))
                {
                    return unsigned(&next);
                }
                let Some(next) = proof.prove_stated_fact(&guard)? else {
                    return Ok(None);
                };
                unsigned(&next)
            }
        }
    }
}

/// The type range of the observation of `value`, a machine value of
/// `format`.
fn range_items(
    value: &ContractExpression,
    format: crate::kernel::MachineIntegerFormat,
) -> Vec<Carried> {
    let (minimum, maximum) = format.bounds();
    let (minimum, maximum) = (minimum.to_string(), maximum.to_string());
    [
        relate(
            integer_literal(&minimum),
            to_integer(value),
            Relation::LessEqual,
        ),
        relate(
            to_integer(value),
            integer_literal(&maximum),
            Relation::LessEqual,
        ),
    ]
    .into_iter()
    .map(|bound| Carried {
        establish: Establish::Steps(vec![have(bound.clone(), vec![type_range(bound.clone())])]),
        surface: bound,
    })
    .collect()
}

/// What `solve`'s connected-equality chain may still spend.
struct RewriteBudget {
    attempts: usize,
    solve_closures: usize,
}

/// How the rewrite search closes each goal it reaches.
#[derive(Clone, Copy)]
pub(in crate::surface::proof) enum RewriteClosers<'p> {
    /// `assumption`, `normalize`, the direct logical closer, then a
    /// bounded nested `solve`: the context's facts.
    Ambient,
    /// The early goal-local route: direct/typed closure and optional
    /// function unfolding, without restarting all of `solve` before arithmetic.
    GoalLocal { allow_function_unfold: bool },
    /// The direct logical closer, `solve`'s typed atomic closer and
    /// `normalize`, for `solve`'s own premises: no nested `solve`, which
    /// would select the same premises and search them again.
    Selected,
    /// `normalize` and an atomic plan over these premises alone, for
    /// `solve() using`, which reads no ambient fact.
    Listed(&'p [(Proposition, ClickProposition)]),
}

/// Whether `kernel` is an equality the `rewrite` step can use.
fn is_rewrite_equality(kernel: &Proposition) -> bool {
    matches!(
        kernel,
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                // An 8- or 16-bit equality rewrites at its own width.
                format: MachineIntegerType::Int32
                    | MachineIntegerType::UInt32
                    | MachineIntegerType::Int64
                    | MachineIntegerType::Int8
                    | MachineIntegerType::UInt8
                    | MachineIntegerType::Int16
                    | MachineIntegerType::UInt16,
                relation: CompareRelation::Equal,
                ..
            },
            true
        ) | Proposition::ConditionIs(
            ConditionTerm::PointerEqual(_, _)
                | ConditionTerm::PointerValueEqual(_, _)
                | ConditionTerm::PointerOffsetEqual(_, _),
            true
        ) | Proposition::Equal(Term::Algebraic(_), Term::Algebraic(_))
    )
}

/// An equality in both directions, each with its kernel form.
fn oriented_forms(
    kernel: Proposition,
    surface: ClickProposition,
) -> Vec<(Proposition, ClickProposition)> {
    // Arithmetic operands need an explicit observation when reparsed under
    // Integer arithmetic. Ordinary equalities retain their source spelling.
    let machine_arithmetic = crate::kernel::machine_integer::representation::is_ring_operation;
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

/// Preserve a native equality's carrier without turning it into an Integer
/// observation. This also makes arithmetic in a recorded source round-trip.
fn explicit_native_rewrite_equality(
    kernel: &Proposition,
    surface: &ClickProposition,
) -> Option<ClickProposition> {
    let Proposition::ConditionIs(ConditionTerm::Compare { format, .. }, _) = kernel else {
        return None;
    };
    fn cast(
        operand: &ContractExpression,
        format: crate::kernel::MachineIntegerType,
    ) -> ContractExpression {
        ContractExpression::CUnary {
            operand: Box::new(operand.clone()),
            lowered: CExpression::Cast {
                expression: Box::new(CExpression::Value(int32(0))),
                target_type: format.c_type(),
                integer_mode: crate::kernel::CIntegerCastMode::CConversion,
                pointee_struct: None,
                pointee_volatile: false,
                pointee_constant: false,
                explicit_qualification: false,
            },
        }
    }
    match surface {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => Some(ClickProposition::Comparison {
            left: cast(left, *format),
            operator: *operator,
            right: cast(right, *format),
        }),
        ClickProposition::At {
            selector,
            proposition,
        } => Some(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(explicit_native_rewrite_equality(kernel, proposition)?),
        }),
        _ => None,
    }
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
    /// The equality `a == b` a disequality goal `a != b` over integers
    /// (machine or `Integer`) denies, in kernel and source form: the fact
    /// `intro()` adds when it opens the goal's refutation.
    pub(in crate::surface::proof) fn disequality_goal_equality(
        &self,
    ) -> Option<(Proposition, ClickProposition)> {
        let kernel = match self.goal()? {
            Proposition::ConditionIs(ConditionTerm::IntegerNotEqual(left, right), true) => {
                Proposition::ConditionIs(
                    ConditionTerm::IntegerEqual(left.clone(), right.clone()),
                    true,
                )
            }
            Proposition::ConditionIs(
                condition @ (ConditionTerm::IntegerEqual(..)
                // An 8- or 16-bit equality is the same fact as the `int32`
                // equality of its widenings (rule K8).
                | ConditionTerm::Compare {
                    format: MachineIntegerType::Int32
                        | MachineIntegerType::UInt32
                        | MachineIntegerType::Int8
                        | MachineIntegerType::UInt8
                        | MachineIntegerType::Int16
                        | MachineIntegerType::UInt16,
                    relation: CompareRelation::Equal,
                    ..
                }
                | ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    ..
                }),
                false,
            ) => Proposition::ConditionIs(condition.clone(), true),
            _ => return None,
        };
        let surface = match self.surface_goal()? {
            ClickProposition::Comparison {
                left,
                operator: ComparisonOperator::NotEqual,
                right,
            } => ClickProposition::Comparison {
                left: left.clone(),
                operator: ComparisonOperator::Equal,
                right: right.clone(),
            },
            ClickProposition::Not(inner)
                if matches!(
                    inner.as_ref(),
                    ClickProposition::Comparison {
                        operator: ComparisonOperator::Equal,
                        ..
                    }
                ) =>
            {
                inner.as_ref().clone()
            }
            _ => return None,
        };
        Some((kernel, surface))
    }

    /// Close a disequality goal `a != b` by refuting `a == b`: `intro()`
    /// adds the equality and leaves `false`, which `arithmetic` proves from
    /// the listed premises and the equality. `None` when the goal is not an
    /// integer disequality.
    pub(in crate::surface::proof) fn disequality_by_refutation(
        &self,
        premises: &[ClickProposition],
    ) -> Option<Result<Self, ClickError>> {
        let (_, equality) = self.disequality_goal_equality()?;
        let introduced = match self.apply_step(ProofStep::Intro) {
            Ok(introduced) => introduced,
            Err(error) => return Some(Err(error)),
        };
        let mut listed = premises.to_vec();
        listed.push(equality);
        Some(introduced.apply_step(ProofStep::ArithmeticUsing(listed)))
    }

    /// `auto`'s route for a disequality goal `a != b`: a linear refutation
    /// of `a == b` leaves `a` on one side of `b`, so prove `a < b`, or else
    /// `b < a`, by selected-premise arithmetic, and refute `a == b` from it.
    pub(in crate::surface::proof) fn try_disequality_by_selected_refutation(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        let Some((_, ClickProposition::Comparison { left, right, .. })) =
            self.disequality_goal_equality()
        else {
            return Ok(None);
        };
        for order in [
            relate(left.clone(), right.clone(), Relation::Less),
            relate(right.clone(), left.clone(), Relation::Less),
        ] {
            check_verification_deadline()?;
            let Ok(scope) = self.begin_have(order.clone()) else {
                continue;
            };
            // An order that is itself a fact is not among the premises the
            // arithmetic selects; `assumption` states it.
            let closed = match scope.apply_step(ProofStep::Assumption) {
                Ok(closed) => closed,
                Err(_) => {
                    let Some(closed) = scope.try_selected_arithmetic()? else {
                        continue;
                    };
                    closed
                }
            };
            let Ok(ordered) = closed.join() else {
                continue;
            };
            if let Some(Ok(closed)) = ordered.disequality_by_refutation(&[order]) {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    /// Close an `Integer` bound goal with selected-premise arithmetic after carrying the
    /// connected machine order facts to `Integer`. Any miss leaves the proof
    /// unchanged.
    pub(in crate::surface::proof) fn try_bridged_selected_arithmetic(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        let (Some(goal), Some(surface_goal)) = (self.goal(), self.surface_goal()) else {
            return Ok(None);
        };
        if !crate::kernel::proof::integer_arithmetic::written_integer_affine_claim(goal) {
            return Ok(None);
        }
        let Some(candidates) =
            crate::surface::planning::proposition_search::arithmetic_connected_premises(
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
            // The operation's own format, from its lowered observation: one
            // rule at every width.
            let surface = relate(to_integer(&operation), exact, Relation::Equal);
            let Some(format) = self
                .lower_cited_surface_proposition(&surface, "planned carried fact")
                .ok()
                .as_ref()
                .and_then(observed_operation_format)
            else {
                continue;
            };
            carried.push(Carried {
                surface,
                establish: Establish::Operation {
                    left: left.as_ref().clone(),
                    right: right.as_ref().clone(),
                    subtract,
                    operation: operation.clone(),
                    format,
                },
            });
            carried.extend(range_items(&operation, format));
        }
        if carried.is_empty() {
            return Ok(None);
        }

        // Lower candidate statements without constructing proofs for them.
        // Only a successful arithmetic plan selects which bridge steps to issue.
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
            let IntegerRefutation::Proved { premises: used, .. } =
                crate::instrumentation::measure_operation(
                    "surface",
                    "solve arithmetic",
                    "solve arithmetic: bridged integer refutation",
                    || refute_integer_goal(goal, &premises, &[]),
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
            // The plan selected the premises; `arithmetic` proves the goal
            // from them. A cited fact with no source spelling cannot be
            // listed, so selected-premise arithmetic does not close the goal.
            let Some(listed) =
                used.iter()
                    .map(|premise| {
                        match planned.iter().enumerate().find(|(index, (kernel, _))| {
                            !rejected.contains(index) && kernel == premise
                        }) {
                            Some((_, (_, item))) => Some(item.surface.clone()),
                            None => proof
                                .resolve_solve_premises(std::slice::from_ref(premise), &[])
                                .and_then(|mut spelled| spelled.pop())
                                .map(|(_, surface)| surface),
                        }
                    })
                    .collect::<Option<Vec<_>>>()
            else {
                return Ok(None);
            };
            return attempt::candidate_outcome(
                proof.apply_step(ProofStep::ArithmeticUsing(listed)),
            );
        }
    }

    /// The equality-by-bounds closure as `solve` tries it early. A plain
    /// 64-bit equality, with no sum or difference on either side, waits for
    /// `solve`'s other strategies and the wide-equality route after them:
    /// proving it by bounds here would run a nested `auto` for each bound
    /// ahead of them.
    pub(in crate::surface::proof) fn try_equality_by_bounds_early(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        if let (
            Some(Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    ..
                },
                true,
            )),
            Some(ClickProposition::Comparison { left, right, .. }),
        ) = (self.goal(), self.surface_goal())
            && !writes_sum_or_difference(left, right)
        {
            return Ok(None);
        }
        self.try_equality_by_bounds()
    }

    /// Close an `Integer` equality goal `l == r` by proving `l <= r` and
    /// `r <= l` with `auto` on each stated fact and joining them with
    /// `equal_from_bounds`. Any miss leaves the proof unchanged.
    pub(in crate::surface::proof) fn try_equality_by_bounds(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        self.equality_by_bounds(false)
    }

    /// [`Self::try_equality_by_bounds`], also for a plain 32-bit
    /// equality when `plain_32_bit`: `auto`'s last route, after the indexed
    /// native-reading route has missed, as it does for an Integer fact such
    /// as `to_integer(i) + 1 == 2`.
    pub(in crate::surface::proof) fn equality_by_bounds(
        &self,
        plain_32_bit: bool,
    ) -> Result<Option<Self>, ClickError> {
        let (Some(goal), Some(surface_goal)) = (self.goal(), self.surface_goal()) else {
            return Ok(None);
        };
        // A plain 32-bit equality, with no sum or difference on either side,
        // already has the indexed native-reading arithmetic route; proving it by
        // bounds would repeat that search for each bound.
        if !plain_32_bit
            && let (
                Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                        relation: CompareRelation::Equal,
                        ..
                    },
                    true,
                ),
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
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal,
                    ..
                },
                true
            )
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
        // A lower bound the facts prove alone needs no operation identity.
        // Otherwise the goal's identities are proved once, here, rather than
        // once inside each bound's `have`, where the first bound's proof of
        // them would be dropped when its `have` closes.
        let Ok(scope) = self.begin_have(lower.clone()) else {
            return Ok(None);
        };
        let mut lower_alone = scope.try_selected_arithmetic_without_identities()?;
        let mut proof = match lower_alone {
            Some(_) => self.clone(),
            None => match self.with_goal_operation_identities(&observed)? {
                // A goal that is one of the identities needs no bounds.
                Some(identities) => {
                    if let Some(closed) =
                        attempt::candidate_outcome(identities.apply_step(ProofStep::Assumption))?
                    {
                        return Ok(Some(closed));
                    }
                    identities
                }
                None => self.clone(),
            },
        };
        for bound in [&lower, &upper] {
            let closed = match lower_alone.take() {
                Some(closed) => closed,
                None => {
                    let Ok(scope) = proof.begin_have(bound.clone()) else {
                        return Ok(None);
                    };
                    let Some(closed) = scope.try_arithmetic_fact_closure()? else {
                        return Ok(None);
                    };
                    closed
                }
            };
            let Ok(joined) = closed.join() else {
                return Ok(None);
            };
            proof = joined;
        }
        attempt::candidate_outcome(proof.apply_step(ProofStep::ArithmeticUsing(vec![lower, upper])))
    }

    /// `auto` on a proposition goal with no C to run: `solve`.
    pub(in crate::surface::proof) fn try_auto_proof_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        self.try_solve_closure()
    }

    /// A goal that restates an available fact through one connected
    /// equality, such as `f(Node(..)) == 1` beside `f(t) == 1` and
    /// `t == Node(..)`: one `rewrite` and `assumption`. `solve` tries it
    /// before the connected-equality chain, which would prove it too, at
    /// greater cost. At most `SINGLE_REWRITES` rewrites.
    pub(in crate::surface::proof) fn try_single_rewrite_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        use crate::kernel::proof::equality_rewrite::{equality_rewrite_applies, reverse_equality};
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        let Some(equalities) = crate::surface::planning::proposition_search::connected_equalities(
            self.facts().assumptions(),
            goal,
        ) else {
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
            let Some(surface) = self.available_rewrite_equality(equality) else {
                continue;
            };
            let kernel = equality.clone();
            let mut forms = Vec::new();
            if let Some(unanchored) = unanchored_equality(&surface)
                && let Ok(lowered) =
                    self.lower_surface_proposition(&unanchored, "`solve` rewrite equality")
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
    /// congruence step `solve` takes only once its decider has selected the
    /// premises, here offered every connected equality, algebraic `==` facts
    /// included. Each rewrite is an ordinary checked step.
    pub(in crate::surface::proof) fn try_connected_equality_chain_closure(
        &self,
        closers: RewriteClosers<'_>,
    ) -> Result<Option<Self>, ClickError> {
        use crate::kernel::proof::equality_rewrite::{equality_rewrite_applies, reverse_equality};
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        let Some(mut equalities) =
            crate::surface::planning::proposition_search::connected_equalities(
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
        let forms = |kernel: Proposition, surface: ClickProposition| {
            let mut forms = oriented_forms(kernel.clone(), surface.clone());
            if matches!(closers, RewriteClosers::GoalLocal { .. })
                && forms
                    .first()
                    .is_some_and(|(_, observed)| observed != &surface)
                && let Some(native) = explicit_native_rewrite_equality(&kernel, &surface)
            {
                // A native rewrite preserves a structural successor in an
                // abstract contract post-state where its Integer observation
                // can change the goal's carrier. Casts keep that native
                // arithmetic explicit when the certificate is reparsed.
                let reverse = reverse_equality(&kernel)
                    .zip(super::fixed_state_proofs::reverse_surface_equality(&native));
                let mut native_forms = vec![(kernel, native)];
                native_forms.extend(reverse);
                native_forms.append(&mut forms);
                return native_forms;
            }
            forms
        };
        let mut candidates: Vec<Vec<(Proposition, ClickProposition)>> = Vec::new();
        for equality in &equalities {
            check_verification_deadline()?;
            if candidates.len() >= REWRITE_EQUALITIES {
                break;
            }
            let Some(surface) = self.available_rewrite_equality(equality) else {
                continue;
            };
            let kernel = equality.clone();
            // A fact recorded at a statement's entry is spelled there; its
            // unanchored form denotes the same fact where the proof stands
            // when nothing it names has changed since, which lowering and
            // the checked rewrite decide. Offer the unanchored form first.
            if let Some(unanchored) = unanchored_equality(&surface)
                && let Ok(lowered) =
                    self.lower_surface_proposition(&unanchored, "`solve` rewrite equality")
            {
                candidates.push(forms(lowered, unanchored));
            }
            candidates.push(forms(kernel, surface));
        }
        if candidates.is_empty() {
            return Ok(None);
        }
        let mut seen = std::collections::BTreeMap::from([(goal.clone(), REWRITE_DEPTH)]);
        let mut budget = RewriteBudget {
            attempts: REWRITE_ATTEMPTS,
            solve_closures: REWRITE_SOLVE_CLOSURES,
        };
        self.rewrite_search(
            &candidates,
            &mut vec![false; candidates.len()],
            REWRITE_DEPTH,
            &mut seen,
            &mut budget,
            closers,
        )
    }

    /// The same search over equalities a step selected or listed instead
    /// of the goal's connected facts: `solve`'s premises from its
    /// derivation, or a `solve() using` list. Each equality is used at most
    /// once, so the chain is as long as the list allows, and `closers`
    /// says what may close a rewritten goal.
    pub(in crate::surface::proof) fn try_premise_equality_chain_closure(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
        closers: RewriteClosers<'_>,
    ) -> Result<Option<Self>, ClickError> {
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        let candidates = premise_pairs
            .iter()
            .filter(|(kernel, _)| is_rewrite_equality(kernel))
            .take(REWRITE_EQUALITIES)
            .map(|(kernel, surface)| oriented_forms(kernel.clone(), surface.clone()))
            .collect::<Vec<_>>();
        if candidates.is_empty() {
            return Ok(None);
        }
        let mut seen = std::collections::BTreeMap::from([(goal.clone(), candidates.len())]);
        let mut budget = RewriteBudget {
            attempts: REWRITE_ATTEMPTS,
            solve_closures: REWRITE_SOLVE_CLOSURES,
        };
        self.rewrite_search(
            &candidates,
            &mut vec![false; candidates.len()],
            candidates.len(),
            &mut seen,
            &mut budget,
            closers,
        )
    }

    /// `auto` on a goal about the fields of a value that two connected facts
    /// equate to constructor applications, `t == Node(c, r)` and
    /// `t == Node(Black, Empty)`: it states `Node(c, r) == Node(Black, Empty)`,
    /// proved by rewriting each application to `t`, and `solve` then reads the
    /// fields' equalities (or the constructors' mismatch) from it. At most
    /// `CONSTRUCTOR_EQUATIONS` connected equations are paired.
    pub(in crate::surface::proof) fn try_constructor_join_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        let Some(equalities) = crate::surface::planning::proposition_search::connected_equalities(
            self.facts().assumptions(),
            goal,
        ) else {
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
                .resolve_solve_premises(std::slice::from_ref(equality), &[])
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
                if let Some(closed) = next.try_solve_closure()? {
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
        let Some(equalities) = crate::surface::planning::proposition_search::connected_equalities(
            self.facts().assumptions(),
            goal,
        ) else {
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
                .resolve_solve_premises(std::slice::from_ref(equality), &[])
                .and_then(|mut spelled| spelled.pop())
            else {
                continue;
            };
            // A fact recorded at an earlier point is spelled there; its
            // unanchored form names the same fact when it lowers to it here.
            let fact = match unanchored_equality(&fact) {
                Some(unanchored)
                    if self
                        .lower_surface_proposition(&unanchored, "`solve` definition fact")
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
                            .lower_surface_proposition(&condition, "`solve` definition condition")
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
                let refute = |steps: Vec<ProofStep>| {
                    self.apply_step(have(refutation.differs.clone(), steps))
                        .and_then(|next| {
                            next.apply_step(ProofStep::Contradiction(refutation.fact.clone()))
                        })
                };
                // The unfolds alone can decide a `Bool` end (Stage 5): the
                // refreshed goal is then a cited condition, and the
                // `normalize` after them has nothing left to prove.
                let mut unfolded = steps.clone();
                unfolded.pop();
                let refuted = refute(steps).or_else(|error| refute(unfolded).map_err(|_| error));
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
        closers: RewriteClosers<'_>,
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
                        if let Some(closed) = rewritten.try_close_after_rewrite(budget, closers)? {
                            return Ok(Some(closed));
                        }
                    }
                }
                seen.insert(goal, left);
                if depth > 1 {
                    used[index] = true;
                    let found = rewritten.rewrite_search(
                        candidates,
                        used,
                        depth - 1,
                        seen,
                        budget,
                        closers,
                    )?;
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
        closers: RewriteClosers<'_>,
    ) -> Result<Option<Self>, ClickError> {
        // Inside a `have`, the stated fact is the focused goal; the proof
        // around it is not complete yet.
        let closes = |proof: &Self| proof.focused_discharged() || proof.is_complete();
        if let RewriteClosers::Listed(premise_pairs) = closers {
            if let Ok(closed) = self.apply_step(ProofStep::Normalize)
                && closes(&closed)
            {
                return Ok(Some(closed));
            }
            return Ok(self
                .try_typed_atomic_solve_from_selected_premises(premise_pairs)
                .filter(closes));
        }
        if let RewriteClosers::GoalLocal {
            allow_function_unfold,
        } = closers
        {
            if let Some(closed) = self
                .try_direct_logical_closure()?
                .or_else(|| self.try_typed_atomic_solve_closure())
                .or_else(|| self.apply_step(ProofStep::Normalize).ok().filter(closes))
            {
                return Ok(Some(closed));
            }
            if !allow_function_unfold || budget.solve_closures == 0 {
                return Ok(None);
            }
            budget.solve_closures -= 1;
            return self.try_function_unfold_solve_closure(&[]);
        }
        if let RewriteClosers::Selected = closers {
            let closed = self
                .try_direct_logical_closure()?
                .or_else(|| self.try_typed_atomic_solve_closure())
                .or_else(|| self.apply_step(ProofStep::Normalize).ok().filter(closes));
            return Ok(closed.filter(closes));
        }
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
        if budget.solve_closures == 0 {
            return Ok(None);
        }
        budget.solve_closures -= 1;
        Ok(self.try_solve_closure()?.filter(closes))
    }

    /// Prove the arithmetic subgoal `fact` where the proof stands, by
    /// arithmetic alone.
    fn prove_stated_fact(&self, fact: &ClickProposition) -> Result<Option<Self>, ClickError> {
        let Ok(scope) = self.begin_have(fact.clone()) else {
            return Ok(None);
        };
        let Some(closed) = scope.try_arithmetic_fact_closure()? else {
            return Ok(None);
        };
        Ok(closed.join().ok())
    }

    /// Close `defined(a + b)` or `defined(a - b)` over `int32` or `int64`:
    /// prove both `Integer` bounds of the exact result by arithmetic.
    /// Together they are the definedness fact, which they file as a fact.
    pub(in crate::surface::proof) fn try_definedness_by_bounds(
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
        // An operand that is itself an operation must be defined too; prove
        // that first so the goal is complete once the outer one is.
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
        // The formats a definedness fact can be stated at, each by its
        // range (`machine_integer::definedness`).
        for ty in crate::kernel::machine_integer::definedness::defined_formats() {
            let (minimum, maximum) = crate::kernel::machine_integer::range::range(ty);
            let lower = ClickProposition::Comparison {
                left: exact.clone(),
                operator: ComparisonOperator::GreaterEqual,
                right: ContractExpression::IntegerLiteral(minimum.to_string()),
            };
            let upper = relate(
                exact.clone(),
                ContractExpression::IntegerLiteral(maximum.to_string()),
                Relation::LessEqual,
            );
            let Some(bounded) = base.prove_stated_fact(&lower)? else {
                continue;
            };
            let Some(bounded) = bounded.prove_stated_fact(&upper)? else {
                continue;
            };
            // The goal may also ask that each operand is defined, which
            // the facts already say.
            if let Some(closed) = bounded.try_direct_logical_closure().ok().flatten() {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    /// Close a machine order goal `a < b` or `a <= b` by proving its
    /// `Integer` reading, the native comparison itself, with selected-premise
    /// arithmetic. Any miss leaves the proof unchanged.
    pub(in crate::surface::proof) fn try_machine_goal_through_integer(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        self.try_machine_goal_through_integer_for(false)
    }

    /// `try_machine_goal_through_integer` for a 64-bit equality goal. Its
    /// `Integer` reading is proved before the type is known, so it costs
    /// more than the other machine goals; `auto` tries it last, after
    /// `solve` and its rewrite search.
    pub(in crate::surface::proof) fn try_wide_equality_through_integer(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        self.try_machine_goal_through_integer_for(true)
    }

    fn try_machine_goal_through_integer_for(
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
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal,
                    ..
                },
                true
            )
        )
        .then(MachineEqualityBridgeScope::enter);
        // A machine comparison is the Integer comparison of its operands'
        // exact observations, so its Integer reading is the goal itself:
        // state each sum or difference defined, as `to_integer` of it needs,
        // and close the goal by `Integer` arithmetic with operation identities.
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
        // Without a stated definedness fact this is the selected-premise arithmetic `solve`
        // already ran on the goal. Plain 32-bit equality, with no sum or
        // difference to observe, already has the indexed native-reading
        // arithmetic route; re-entering it by bounds repeats equality-by-bounds
        // and snapshot search for the same comparison.
        if !stated && !wide_equality {
            return Ok(None);
        }
        // Simplex refutes bounds; an equality is proved from its two.
        if relation == Relation::Equal {
            return base.try_equality_by_bounds();
        }
        base.selected_arithmetic(true, &[])
    }

    /// The sums and differences named by connected complete arithmetic domains.
    fn defined_operations(&self, candidates: &[Proposition]) -> Vec<ContractExpression> {
        fn operation(surface: ClickProposition) -> Option<ContractExpression> {
            match surface {
                ClickProposition::Defined { expression } => match expression {
                    ContractExpression::Add(..) | ContractExpression::Subtract(..) => {
                        Some(expression)
                    }
                    _ => None,
                },
                ClickProposition::At {
                    selector,
                    proposition,
                } => {
                    let anchor = |expression| {
                        Box::new(ContractExpression::At {
                            selector: selector.clone(),
                            expression,
                        })
                    };
                    match operation(*proposition)? {
                        ContractExpression::Add(a, b) => {
                            Some(ContractExpression::Add(anchor(a), anchor(b)))
                        }
                        ContractExpression::Subtract(a, b) => {
                            Some(ContractExpression::Subtract(anchor(a), anchor(b)))
                        }
                        _ => None,
                    }
                }
                _ => None,
            }
        }
        let mut operations = Vec::new();
        let mut seen = std::collections::HashSet::new();
        for candidate in candidates {
            // Select the operation structurally from either ordinary bound.
            // The private query supplies its format and operands, not evidence.
            // Naming uses the same indexed states as structural goal spelling;
            // it does not require a recorded `defined(...)` source. The actual
            // observation theorem still proves the complete ordinary domain.
            let query = crate::kernel::machine_integer::definedness::definedness_of_integer_bound(
                candidate,
            )
            .unwrap_or_else(|| candidate.clone());
            if !matches!(
                &query,
                Proposition::ConditionIs(
                    ConditionTerm::Overflows {
                        format: MachineIntegerType::Int32 | MachineIntegerType::Int64,
                        op: OverflowOperation::Add | OverflowOperation::Subtract,
                        ..
                    },
                    false
                )
            ) || !seen.insert(query.clone())
            {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            if let Some(surface) = self.structural_proposition_candidate(&query)
                && let Some(operation) = operation(surface)
            {
                operations.push(operation);
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
            // arithmetic call.
            let Some(order) =
                MachineOrder::of(candidate).filter(|order| *order != MachineOrder::Equal64)
            else {
                continue;
            };
            crate::instrumentation::record_deterministic_work(1);
            let Some(spelled) = self.resolve_solve_premises(std::slice::from_ref(candidate), &[])
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
            let observed = relate(to_integer(&lower), to_integer(&upper), relation);
            let carry = match relation {
                // A comparison of exact observations is the native
                // comparison itself, a fact already.
                Relation::Less | Relation::LessEqual => vec![ProofStep::Assumption],
                // Equal values have equal observations: rewriting by the
                // fact, stated the way round it is written, leaves an
                // identity.
                Relation::Equal => {
                    let stated = relate(lower.clone(), upper.clone(), relation);
                    vec![ProofStep::Rewrite(stated), ProofStep::Normalize]
                }
            };
            let steps = vec![have(observed.clone(), carry)];
            carried.push(Carried {
                establish: Establish::Steps(steps),
                surface: observed,
            });
            if let Some((minimum, maximum)) = order.range() {
                for value in [lower, upper] {
                    if matches!(to_integer(&value), ContractExpression::IntegerLiteral(_))
                        || ranged.contains(&value)
                    {
                        continue;
                    }
                    ranged.push(value.clone());
                    for bound in [
                        relate(
                            integer_literal(&minimum),
                            to_integer(&value),
                            Relation::LessEqual,
                        ),
                        relate(
                            to_integer(&value),
                            integer_literal(&maximum),
                            Relation::LessEqual,
                        ),
                    ] {
                        carried.push(Carried {
                            establish: Establish::Steps(vec![have(
                                bound.clone(),
                                vec![type_range(bound.clone())],
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
    include!("../../scaling_tests/surface/proof/selected_arithmetic.rs");
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check_listed_operation_identity(ty: &str, bound: &str, operation: &str) {
        let op = if operation.contains('+') { "+" } else { "-" };
        let source = format!(
            r#"
theorem identity(x: {ty}) {{
    requires {bound};
    ensures to_integer({operation}) == to_integer(x) {op} 1 by {{
        solve() using {{ {bound}; }};
    }}
}}
"#
        );
        crate::surface::verify_click_theorems(&source).unwrap();
        let line = source
            .lines()
            .position(|line| line.contains("solve()"))
            .unwrap();
        let column = source.lines().nth(line).unwrap().find("solve()").unwrap();
        let expanded =
            crate::surface::expand_c0_tactic_source_at(&source, &[], line + 1, column + 1).unwrap();
        assert!(
            expanded.contains("integer_operation_identity"),
            "{expanded}"
        );
        without_implicit_auto(|| crate::surface::verify_click_theorems(&expanded)).unwrap();
        let omitted = source.replace(&format!("using {{ {bound}; }}"), "using {}");
        assert!(
            crate::surface::verify_click_theorems(&omitted).is_err(),
            "an unlisted no-wrap bound must not be read: {omitted}"
        );
    }

    #[test]
    fn listed_premises_prove_signed_add_identity() {
        check_listed_operation_identity("int32", "x < 2147483647", "x + 1");
    }

    #[test]
    fn listed_premises_prove_signed_subtract_identity() {
        check_listed_operation_identity("int32", "x > -2147483648", "x - 1");
    }

    #[test]
    fn listed_premises_prove_unsigned_add_identity() {
        check_listed_operation_identity("uint64", "x < 18446744073709551615u64", "x + 1u64");
    }

    #[test]
    fn listed_premises_prove_unsigned_subtract_identity() {
        check_listed_operation_identity("uint64", "x > 0u64", "x - 1u64");
    }

    #[test]
    fn auto_proves_an_equality_operation_identity_once() {
        // Each bound of the split equality is proved inside its own `have`,
        // which drops the identities proved there, so proving them per bound
        // would prove `to_integer(x + 1) == to_integer(x) + 1` twice.
        let source = r#"
theorem successor_identity(x: int32) {
    requires x < 2147483647;
    ensures to_integer(x + 1) == to_integer(x) + 1 by {
        have to_integer(x + 1) == to_integer(x) + 1 by solve();
        assumption();
    }
}
"#;
        crate::surface::verify_click_theorems(source).unwrap();
        let line = source
            .lines()
            .position(|line| line.contains("by solve()"))
            .unwrap();
        let column = source.lines().nth(line).unwrap().find("solve()").unwrap();
        let expanded =
            crate::surface::expand_c0_tactic_source_at(source, &[], line + 1, column + 1).unwrap();
        assert_eq!(
            expanded.matches("integer_operation_identity").count(),
            1,
            "{expanded}"
        );
        crate::surface::verify_click_theorems(&expanded).unwrap();
    }

    /// `solve` reaches its simplification before splitting a plain 64-bit
    /// equality into its two bounds, each of which would run a nested search.
    #[test]
    fn auto_leaves_a_plain_64_bit_equality_to_solve() {
        let source = r#"spec enum Color { Red, Black, }
function color_bit(color: Color) -> int32 {
    match color { Color::Red => 0, Color::Black => 1, }
}
theorem low_bit_is_the_color_bit(bits: uint64, color: Color) {
    requires (bits & 1u64) == color_bit(color) as uint64;
    ensures (bits & 1u64) == color_bit(color) as uint64 by {
        have (bits & 1u64) == color_bit(color) as uint64 by solve();
        assumption();
    }
}
"#;
        crate::surface::verify_click_theorems(source).unwrap();
        let line = source
            .lines()
            .position(|line| line.contains("by solve()"))
            .unwrap();
        let column = source.lines().nth(line).unwrap().find("solve()").unwrap();
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
                have not(color_black(Color::Red) == 1);
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

    /// The connected-equality rewrite search is `solve`'s, so `solve()` alone
    /// proves what used to need `auto()`.
    #[test]
    fn solve_runs_the_connected_equality_rewrite_search() {
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
                have not(color_black(Color::Red) == 1) by solve();
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
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(capacity),
                right: Box::new(binary_node!(Int32, Add, Box::new(used), Box::new(slots))),
            },
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
