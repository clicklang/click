use super::*;
use crate::kernel::machine_integer::{
    Relation,
    comparison::{ComparisonOperand, NativeComparisonView},
};
use crate::kernel::{MachineOperandView as V, SharedMachineIntegerTerm};
use crate::kernel::{constant_u32, int32_constant};

/// One collected order fact: `left (<|<=) right` with its strictness.
pub(in crate::kernel) type OrderFact = (OrderOperand, OrderOperand, bool);
pub(in crate::kernel) type OrderOperand = super::super::checked_scalar_facts::ScalarOperandKey;

pub(in crate::kernel::assumptions) fn retain_order_operand(view: V<'_>) -> OrderOperand {
    match view {
        V::Legacy(term) => OrderOperand::Written(term.clone()),
        V::Shared(_) => OrderOperand::for_format(MachineIntegerType::Int32, view),
    }
}

pub(in crate::kernel::assumptions) fn retained_order_fact(
    condition: &ConditionTerm,
    truth: bool,
) -> Option<OrderFact> {
    let view = order_view_at_format(condition, truth, MachineIntegerType::Int32)?;
    Some((
        retain_order_operand(view.operands[0].operand_view()),
        retain_order_operand(view.operands[1].operand_view()),
        view.relation == Relation::Less,
    ))
}

thread_local! {
    // Order-path queries re-collect the same order facts from the same fact
    // set dozens of times inside one tactic; the collection is a pure
    // per-fact syntactic filter, so it is shared by fact-set content
    // identity. An `Rc` hands every query the same collected vector without
    // re-cloning the terms.
    static ORDER_FACTS_MEMO: std::cell::RefCell<
        std::collections::HashMap<u64, std::rc::Rc<Vec<OrderFact>>>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

const ORDER_FACTS_MEMO_LIMIT: usize = 20_000;

thread_local! {
    static BOUND_SEARCH_DECIDING: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Marks the one nested decision an outermost bound search may make; `None`
/// when a decision is already open under a bound search.
struct NestedBoundSearch;

/// The 32-bit order a bound search reads: signed, from
/// `signed_order_bounds`, or unsigned, from `uint32_order_bounds`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum OrderKind {
    Signed32,
    Unsigned32,
}

impl OrderKind {
    /// The order condition `lower < upper` (strict) or `lower <= upper`.
    pub(in crate::kernel) fn order(
        self,
        lower: MachineTerm,
        upper: MachineTerm,
        strict: bool,
    ) -> ConditionTerm {
        match (self, strict) {
            (Self::Signed32, _) => order_condition(lower, upper, strict),
            (Self::Unsigned32, true) => ConditionTerm::unsigned_less_than(lower, upper),
            (Self::Unsigned32, false) => ConditionTerm::unsigned_less_equal(lower, upper),
        }
    }
}

impl NestedBoundSearch {
    fn enter() -> Option<Self> {
        (!BOUND_SEARCH_DECIDING.with(|deciding| deciding.replace(true))).then(|| Self)
    }
}

impl Drop for NestedBoundSearch {
    fn drop(&mut self) {
        BOUND_SEARCH_DECIDING.with(|deciding| deciding.set(false));
    }
}

#[cfg(test)]
thread_local! {
    // Order facts the lower-bound search has compared with its term, so a
    // regression can pin that unrelated facts are never visited.
    static LOWER_BOUND_CANDIDATE_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

impl PureFactContext {
    #[cfg(test)]
    pub(in crate::kernel) fn reset_lower_bound_candidate_visits() {
        LOWER_BOUND_CANDIDATE_VISITS.with(|visits| visits.set(0));
    }

    #[cfg(test)]
    pub(in crate::kernel) fn lower_bound_candidate_visits() -> usize {
        LOWER_BOUND_CANDIDATE_VISITS.with(std::cell::Cell::get)
    }

    /// Collect the order facts one *named* proposition states outright.
    ///
    /// The walk is structural: conjunction splits, and a guard is consumed
    /// only when the exact index, the intrinsic rule, or the retained
    /// condition checker decides it. There is no prover call and no scan of
    /// the ambient fact set, so an order fact that a proof has not made
    /// available stays invisible to the theory (package 13 of
    /// `docs/internals/proof-objects.md`).
    pub(in crate::kernel) fn collect_derived_order_facts_from_proposition(
        &self,
        proposition: &Proposition,
        order_facts: &mut Vec<OrderFact>,
    ) {
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                if let Some(order_fact) = retained_order_fact(condition, *value) {
                    order_facts.push(order_fact);
                }
            }
            Proposition::And(left, right) => {
                self.collect_derived_order_facts_from_proposition(left, order_facts);
                self.collect_derived_order_facts_from_proposition(right, order_facts);
            }
            Proposition::Implies(left, right) if self.guard_is_decided(left) => {
                self.collect_derived_order_facts_from_proposition(right, order_facts);
            }
            Proposition::ForAll { .. } => {
                self.collect_finite_forall_order_facts(proposition, order_facts);
            }
            _ => {}
        }
    }

    /// Whether a guard is discharged without a proof search. Conjunction
    /// splits structurally; a leaf that is one bare condition goes to the
    /// retained condition checker, and every other leaf must be exactly
    /// available. No logical structure below a conjunction is introduced and
    /// no general prover runs.
    fn guard_is_decided(&self, guard: &Proposition) -> bool {
        match guard {
            Proposition::And(left, right) => {
                self.guard_is_decided(left) && self.guard_is_decided(right)
            }
            Proposition::ConditionIs(condition, value) => {
                PureFactContext::decide_intrinsically(condition) == Some(*value)
                    || self.exact_condition_value(condition) == Some(*value)
                    || !self.should_defer_non_exact_condition_reasoning()
                        && self.decide(condition) == Some(*value)
            }
            _ => self.proves_exact(guard),
        }
    }

    pub(in crate::kernel) fn collect_finite_forall_order_facts(
        &self,
        proposition: &Proposition,
        order_facts: &mut Vec<OrderFact>,
    ) {
        let mut variables = Vec::new();
        let body = collect_forall_chain(proposition, &mut variables);
        if variables.is_empty() {
            return;
        }
        let Some(ranges) = finite_forall_ranges(&variables, body) else {
            return;
        };
        let Some(instantiation_count) = ranges.iter().try_fold(1usize, |count, range| {
            let width = usize::try_from(range.upper - range.lower + 1).ok()?;
            count.checked_mul(width)
        }) else {
            return;
        };
        crate::instrumentation::record_deterministic_work(instantiation_count);

        let mut values = Vec::with_capacity(variables.len());
        self.collect_finite_forall_order_fact_instantiations(
            body,
            &variables,
            &ranges,
            &mut values,
            order_facts,
        );
    }

    pub(in crate::kernel) fn collect_finite_forall_order_fact_instantiations(
        &self,
        body: &Proposition,
        variables: &[Variable],
        ranges: &[FiniteForAllRange],
        values: &mut Vec<i64>,
        order_facts: &mut Vec<OrderFact>,
    ) {
        if values.len() == variables.len() {
            let mut instantiated = body.clone();
            for ((variable, value), range) in variables.iter().zip(values.iter()).zip(ranges) {
                instantiated = substitute_bitvector_variable_in_proposition(
                    &instantiated,
                    *variable,
                    &range.constant(*value),
                );
            }
            self.collect_derived_order_facts_from_proposition(&instantiated, order_facts);
            return;
        }

        let range = &ranges[values.len()];
        for value in range.lower..=range.upper {
            values.push(value);
            self.collect_finite_forall_order_fact_instantiations(
                body,
                variables,
                ranges,
                values,
                order_facts,
            );
            values.pop();
        }
    }

    /// Whether a recorded `uint32` bound proves `lower < upper` (strict) or
    /// `lower <= upper`: an upper bound of `lower` at or below `upper`, or a
    /// lower bound of `upper` at or above `lower`, each judged as
    /// [`Self::bound_proves_order_views`] judges, so the search never recurses
    /// along a chain of bounds.
    pub(in crate::kernel) fn has_unsigned32_bound_between_views(
        &self,
        lower: V<'_>,
        upper: V<'_>,
        strict: bool,
    ) -> bool {
        let kind = OrderKind::Unsigned32;
        self.bounds_for_search_view(kind, lower, true)
            .into_iter()
            .any(|(bound, bound_strict)| {
                self.bound_proves_order_views(
                    kind,
                    bound.operand_view(),
                    upper,
                    strict && !bound_strict,
                )
            })
            || self
                .bounds_for_search_view(kind, upper, false)
                .into_iter()
                .any(|(bound, bound_strict)| {
                    self.bound_proves_order_views(
                        kind,
                        lower,
                        bound.operand_view(),
                        strict && !bound_strict,
                    )
                })
    }

    /// Whether a recorded upper bound of `left` lies at or below `right`
    /// (below it when the bound is not strict), so `left < right`.
    pub(in crate::kernel) fn has_upper_bound_below(
        &self,
        left: &MachineTerm,
        right: &MachineTerm,
    ) -> bool {
        self.has_upper_bound_below_views(V::Legacy(left), V::Legacy(right))
    }

    pub(in crate::kernel) fn has_upper_bound_below_views(&self, left: V<'_>, right: V<'_>) -> bool {
        self.bounds_for_search_view(OrderKind::Signed32, left, true)
            .into_iter()
            .any(|(upper, strict)| {
                self.bound_proves_order_views(
                    OrderKind::Signed32,
                    upper.operand_view(),
                    right,
                    !strict,
                )
            })
    }

    /// Whether a recorded upper bound of `left` lies at or below `right`, so
    /// `left <= right`.
    pub(in crate::kernel) fn has_upper_bound_at_or_below(
        &self,
        left: &MachineTerm,
        right: &MachineTerm,
    ) -> bool {
        self.has_upper_bound_at_or_below_views(V::Legacy(left), V::Legacy(right))
    }

    pub(in crate::kernel) fn has_upper_bound_at_or_below_views(
        &self,
        left: V<'_>,
        right: V<'_>,
    ) -> bool {
        self.bounds_for_search_view(OrderKind::Signed32, left, true)
            .into_iter()
            .any(|(upper, _)| {
                self.bound_proves_order_views(
                    OrderKind::Signed32,
                    upper.operand_view(),
                    right,
                    false,
                )
            })
    }

    /// `left < right` from a recorded `left < right + 1` and a recorded
    /// `left != right`.
    pub(super) fn has_successor_upper_bound_below_views(&self, left: V<'_>, right: V<'_>) -> bool {
        self.bounds_for_search_view(OrderKind::Signed32, left, true)
            .into_iter()
            .any(|(upper, strict)| {
                strict
                    && shared_successor_of(upper.operand_view(), right)
                    && self.has_written_operand_comparison(
                        MachineIntegerType::Int32,
                        crate::kernel::CompareRelation::Equal,
                        left,
                        right,
                        false,
                    )
            })
    }

    pub(super) fn has_add_const_upper_bound_below_views(&self, left: V<'_>, right: V<'_>) -> bool {
        let Some((base, addend)) = left.int32_add_const_parts() else {
            return false;
        };
        if self.decide_const_offset_overflow(base, addend, false) != Some(false) {
            return false;
        }
        // `base < upper` gives `left < upper + addend`, so `upper + addend
        // <= right` is enough; `base <= upper` needs `upper + addend < right`.
        self.bounds_for_search_view(OrderKind::Signed32, base, true)
            .into_iter()
            .any(|(upper, strict)| {
                shared_signed_const_add(upper.operand_view(), addend).is_some_and(|upper| {
                    self.bound_proves_order_views(
                        OrderKind::Signed32,
                        V::Legacy(&upper),
                        right,
                        !strict,
                    )
                })
            })
    }

    pub(super) fn has_add_const_upper_bound_at_or_below_views(
        &self,
        left: V<'_>,
        right: V<'_>,
    ) -> bool {
        let Some((base, addend)) = left.int32_add_const_parts() else {
            return false;
        };
        if self.decide_const_offset_overflow(base, addend, false) != Some(false) {
            return false;
        }
        self.bounds_for_search_view(OrderKind::Signed32, base, true)
            .into_iter()
            .any(|(upper, _)| {
                shared_signed_const_add(upper.operand_view(), addend).is_some_and(|upper| {
                    self.bound_proves_order_views(
                        OrderKind::Signed32,
                        V::Legacy(&upper),
                        right,
                        false,
                    )
                })
            })
    }

    /// `base - c <= right` (or `<` when `strict_goal`) from a recorded
    /// constant upper bound `base <= upper` (or `base < upper`) with
    /// `upper - c <= right` (resp. `<`), when `base - c` does not signed
    /// underflow. The subtraction twin of `has_add_const_upper_bound_*`: an
    /// upper bound on `n` bounds `n - 1` only once `n - 1` is known not to
    /// wrap (at `n = INT_MIN` it is `INT_MAX`).
    ///
    /// The upper bounds of `base` are read from `signed_order_bounds` at
    /// `base` (and its canonical form), so the cost is the bounds recorded at
    /// that one term, not the ambient fact count.
    pub(super) fn has_subtract_const_upper_bound_views(
        &self,
        left: V<'_>,
        right: V<'_>,
        strict_goal: bool,
    ) -> bool {
        let Some((base, subtrahend)) = left.int32_subtract_const_parts() else {
            return false;
        };
        let Ok(subtrahend_value) = i32::try_from(subtrahend) else {
            return false;
        };
        if subtrahend_value <= 0 {
            return false;
        }
        let upper_bounds = self.constant_bounds_for_search_view(base, true);
        if upper_bounds.is_empty()
            || self.decide_const_offset_overflow(base, subtrahend, true) != Some(false)
        {
            return false;
        }
        upper_bounds.into_iter().any(|(upper, strict_fact)| {
            let Some(shifted) = (upper as i32).checked_sub(subtrahend_value) else {
                return false;
            };
            let shifted = MachineTerm::constant(shifted as u32);
            // `base < upper` gives `base - c < upper - c`; `base <= upper`
            // gives `base - c <= upper - c`.
            self.decide_operand_comparison(
                MachineIntegerType::Int32,
                if strict_goal && !strict_fact {
                    Relation::Less
                } else {
                    Relation::LessEqual
                },
                V::Legacy(&shifted),
                right,
            ) == Some(true)
        })
    }

    /// `bound <= base - c` (or `<` when `strict_goal`) from a recorded
    /// constant lower bound `lower <= base` (or `lower < base`) with
    /// `bound <= lower - c` (resp. `<`). `lower - c` is computed without
    /// wrapping, and `base >= lower` then keeps `base - c` from wrapping, so
    /// no separate underflow decision is needed.
    pub(super) fn has_subtract_const_lower_bound_views(
        &self,
        term: V<'_>,
        bound: V<'_>,
        strict_goal: bool,
    ) -> bool {
        let Some((base, subtrahend)) = term.int32_subtract_const_parts() else {
            return false;
        };
        let Ok(subtrahend_value) = i32::try_from(subtrahend) else {
            return false;
        };
        if subtrahend_value <= 0 {
            return false;
        }
        let lower_bounds = self.constant_bounds_for_search_view(base, false);
        lower_bounds.into_iter().any(|(lower, strict_fact)| {
            let Some(shifted) = (lower as i32).checked_sub(subtrahend_value) else {
                return false;
            };
            let shifted = MachineTerm::constant(shifted as u32);
            self.decide_operand_comparison(
                MachineIntegerType::Int32,
                if strict_goal && !strict_fact {
                    Relation::Less
                } else {
                    Relation::LessEqual
                },
                bound,
                V::Legacy(&shifted),
            ) == Some(true)
        })
    }

    pub(super) fn subtract_same_const_order_fact_views(
        &self,
        left: V<'_>,
        right: V<'_>,
        strict: bool,
    ) -> bool {
        let Some((left_base, left_const)) = left.int32_subtract_const_parts() else {
            return false;
        };
        let Some((right_base, right_const)) = right.int32_subtract_const_parts() else {
            return false;
        };
        if left_const != right_const {
            return false;
        }
        // `base - const` wraps; an order between the bases only carries to
        // the subtracted terms when neither subtraction signed underflows
        // (otherwise `a < b` would prove `a - 1 < b - 1`, false at
        // a = INT_MIN, b = INT_MIN + 1).
        if self.decide_const_offset_overflow(left_base, left_const, true) != Some(false)
            || self.decide_const_offset_overflow(right_base, right_const, true) != Some(false)
        {
            return false;
        }

        if strict {
            self.has_written_operand_comparison(
                MachineIntegerType::Int32,
                crate::kernel::CompareRelation::LessThan,
                left_base,
                right_base,
                true,
            ) || self.has_written_operand_comparison(
                MachineIntegerType::Int32,
                crate::kernel::CompareRelation::GreaterThan,
                right_base,
                left_base,
                true,
            )
        } else {
            self.has_written_operand_comparison(
                MachineIntegerType::Int32,
                crate::kernel::CompareRelation::LessEqual,
                left_base,
                right_base,
                true,
            ) || self.has_written_operand_comparison(
                MachineIntegerType::Int32,
                crate::kernel::CompareRelation::GreaterEqual,
                right_base,
                left_base,
                true,
            )
        }
    }

    /// The upper bounds of `term` as `(upper, strict)`, selected by its
    /// written and canonical endpoint keys. Equal-but-differently-spelled
    /// endpoints require an explicit equality or bound, never a fact scan.
    /// The bounds of `term` in the order of `kind`, upper bounds when
    /// `upper` and lower bounds otherwise, from that order's endpoint index
    /// (`signed_order_bounds`, `uint32_order_bounds`) at `term` and its
    /// canonical form.
    pub(super) fn bounds_for_search_view(
        &self,
        kind: OrderKind,
        term: V<'_>,
        upper: bool,
    ) -> Vec<(SharedMachineIntegerTerm, bool)> {
        let index = match kind {
            OrderKind::Signed32 => &self.signed_order_bounds,
            OrderKind::Unsigned32 => &self.uint32_order_bounds,
        };
        // Only written terms have a separate canonical spelling. Shared roots
        // are queried directly; their endpoint keys preserve DAG identity.
        let canonical = match term {
            V::Legacy(term) => Some(crate::kernel::eval::canonical_term(term)),
            V::Shared(_) => None,
        };
        let mut keys = vec![term];
        if let (V::Legacy(written), Some(canonical)) = (term, canonical.as_ref())
            && written != canonical
        {
            keys.push(V::Legacy(canonical));
        }
        let mut bounds = Vec::new();
        for key in keys {
            let Some(entries) = index.get_operand(key) else {
                continue;
            };
            for (_, other, strict, own_is_lower) in entries.operand_keys() {
                crate::instrumentation::record_deterministic_work(1);
                #[cfg(test)]
                if !upper {
                    LOWER_BOUND_CANDIDATE_VISITS.with(|visits| visits.set(visits.get() + 1));
                }
                if own_is_lower == upper {
                    let format = match kind {
                        OrderKind::Signed32 => MachineIntegerType::Int32,
                        OrderKind::Unsigned32 => MachineIntegerType::UInt32,
                    };
                    let other = other.retain(format);
                    if !bounds.contains(&(other.clone(), strict)) {
                        bounds.push((other, strict));
                    }
                }
            }
        }
        bounds
    }

    /// Whether a recorded bound proves `lower <= upper` (or `<` when
    /// `strict`). The outermost bound search judges each bound with one
    /// nested decision; a bound search reached from inside that decision
    /// judges with constants, an exact fact, or the difference graph only.
    /// So a search never recurses along a chain of bounds: its cost is its
    /// term's bounds times one decision that starts no further search.
    fn bound_proves_order_views(
        &self,
        kind: OrderKind,
        lower: V<'_>,
        upper: V<'_>,
        strict: bool,
    ) -> bool {
        let constant = |operand: V<'_>| {
            operand.word32_constant().map(|word| match kind {
                OrderKind::Signed32 => i64::from(word as i32),
                OrderKind::Unsigned32 => i64::from(word),
            })
        };
        let constants = constant(lower).zip(constant(upper));
        if let Some((lower, upper)) = constants {
            return if strict {
                lower < upper
            } else {
                lower <= upper
            };
        }
        let condition = match (lower, upper) {
            (V::Legacy(lower), V::Legacy(upper)) => {
                kind.order(lower.clone(), upper.clone(), strict)
            }
            _ => {
                let format = match kind {
                    OrderKind::Signed32 => MachineIntegerType::Int32,
                    OrderKind::Unsigned32 => MachineIntegerType::UInt32,
                };
                NativeComparisonView {
                    format,
                    relation: if strict {
                        Relation::Less
                    } else {
                        Relation::LessEqual
                    },
                    operands: [lower, upper]
                        .map(|operand| ComparisonOperand::Observation(operand.retain(format))),
                }
                .integer_condition()
            }
        };
        if self.exact_condition_value(&condition) == Some(true)
            || self.difference_graph_proves(&condition)
        {
            return true;
        }
        let Some(_nested) = NestedBoundSearch::enter() else {
            return false;
        };
        self.decide(&condition) == Some(true)
    }

    /// Whether a recorded lower bound of `left` lies above `right`, so
    /// `left > right`.
    pub(in crate::kernel) fn has_lower_bound_above(
        &self,
        left: &MachineTerm,
        right: &MachineTerm,
    ) -> bool {
        self.has_lower_bound_above_views(V::Legacy(left), V::Legacy(right))
    }

    pub(in crate::kernel) fn has_lower_bound_above_views(&self, left: V<'_>, right: V<'_>) -> bool {
        self.bounds_for_search_view(OrderKind::Signed32, left, false)
            .into_iter()
            .any(|(lower, strict)| {
                // `lower < left` and `lower >= right`, or `lower <= left` and
                // `lower > right`, give `left > right`.
                self.bound_proves_order_views(
                    OrderKind::Signed32,
                    right,
                    lower.operand_view(),
                    !strict,
                )
            })
    }

    /// Whether a recorded lower bound of `left` lies at or above `right`, so
    /// `left >= right`.
    pub(in crate::kernel) fn has_lower_bound_at_or_above(
        &self,
        left: &MachineTerm,
        right: &MachineTerm,
    ) -> bool {
        self.has_lower_bound_at_or_above_views(V::Legacy(left), V::Legacy(right))
    }

    pub(in crate::kernel) fn has_lower_bound_at_or_above_views(
        &self,
        left: V<'_>,
        right: V<'_>,
    ) -> bool {
        self.bounds_for_search_view(OrderKind::Signed32, left, false)
            .into_iter()
            .any(|(lower, _)| {
                self.bound_proves_order_views(
                    OrderKind::Signed32,
                    right,
                    lower.operand_view(),
                    false,
                )
            })
    }

    pub(super) fn has_add_const_lower_bound_above_views(&self, left: V<'_>, right: V<'_>) -> bool {
        let Some((base, addend)) = left.int32_add_const_parts() else {
            return false;
        };
        // `base + addend` wraps in two's complement, so a bound on `base`
        // only carries to `base + addend` when that sum does not signed
        // overflow. Without this guard `x >= 0` would wrongly prove
        // `x + 1 > 0` (false at x = INT_MAX). See constant_offset_is_proven.
        if self.decide_const_offset_overflow(base, addend, false) != Some(false) {
            return false;
        }
        // `lower < base` gives `lower + addend < left`, so `right <= lower +
        // addend` is enough; `lower <= base` needs `right < lower + addend`.
        self.bounds_for_search_view(OrderKind::Signed32, base, false)
            .into_iter()
            .any(|(lower, strict)| {
                shared_signed_const_add(lower.operand_view(), addend).is_some_and(|lower| {
                    self.bound_proves_order_views(
                        OrderKind::Signed32,
                        right,
                        V::Legacy(&lower),
                        !strict,
                    )
                })
            })
    }

    pub(super) fn has_add_const_lower_bound_at_or_above_views(
        &self,
        left: V<'_>,
        right: V<'_>,
    ) -> bool {
        let Some((base, addend)) = left.int32_add_const_parts() else {
            return false;
        };
        // `base + addend` wraps; only carry the bound when it does not
        // signed overflow (otherwise `x >= 0` would prove `x + 1 >= 1`,
        // false at x = INT_MAX).
        if self.decide_const_offset_overflow(base, addend, false) != Some(false) {
            return false;
        }
        self.bounds_for_search_view(OrderKind::Signed32, base, false)
            .into_iter()
            .any(|(lower, _)| {
                shared_signed_const_add(lower.operand_view(), addend).is_some_and(|lower| {
                    self.bound_proves_order_views(
                        OrderKind::Signed32,
                        right,
                        V::Legacy(&lower),
                        false,
                    )
                })
            })
    }

    fn constant_bounds_for_search_view(&self, term: V<'_>, upper: bool) -> Vec<(u32, bool)> {
        let canonical = match term {
            V::Legacy(term) => Some(crate::kernel::eval::canonical_term(term)),
            V::Shared(_) => None,
        };
        let mut keys = vec![term];
        if let (V::Legacy(written), Some(canonical)) = (term, canonical.as_ref())
            && written != canonical
        {
            keys.push(V::Legacy(canonical));
        }
        let mut bounds = Vec::new();
        for key in keys {
            let Some(entries) = self.signed_order_bounds.get_operand(key) else {
                continue;
            };
            for (_, other, strict, own_is_lower) in entries.operand_keys() {
                if own_is_lower == upper
                    && let Some(value) = other.word32_constant()
                    && !bounds.contains(&(value, strict))
                {
                    crate::instrumentation::record_deterministic_work(1);
                    bounds.push((value, strict));
                }
            }
        }
        bounds
    }

    fn decide_const_offset_overflow(
        &self,
        base: V<'_>,
        offset: u32,
        subtract: bool,
    ) -> Option<bool> {
        use crate::kernel::machine_integer::{Operation, definedness::OverflowQueryView};
        let literal = MachineTerm::constant(offset);
        if let V::Legacy(base) = base {
            let condition = if subtract {
                ConditionTerm::signed_subtract_overflows(base.clone(), literal)
            } else {
                ConditionTerm::signed_add_overflows(base.clone(), literal)
            };
            return self.decide(&condition);
        }
        let query = OverflowQueryView::from_operands(
            MachineIntegerType::Int32,
            if subtract {
                Operation::Subtract
            } else {
                Operation::Add
            },
            [base, V::Legacy(&literal)],
        )?;
        self.decide_overflow_query(&query)
    }

    /// The existing constant-offset order rule, over either operand representation.
    /// Match only the operation root before reading the base's range or domain.
    pub(super) fn constant_offset_is_proven(
        &self,
        base: V<'_>,
        term: V<'_>,
        subtract: bool,
        strict: bool,
    ) -> bool {
        use crate::kernel::MachineBinaryOp as Op;
        use crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey as Key;
        let Some((MachineIntegerType::Int32, op, [a, b])) = term.binary() else {
            return false;
        };
        if op != if subtract { Op::Subtract } else { Op::Add } {
            return false;
        }
        let (term_base, addend) = match (a.literal(), b.literal()) {
            (_, Some(int32_constant!(n))) => (a, constant_u32(n)),
            (Some(int32_constant!(n)), _) if !subtract => (b, constant_u32(n)),
            _ => return false,
        };
        if nonnegative_int32_value(addend).is_none_or(|n| n < i64::from(strict))
            || Key::canonical(MachineIntegerType::Int32, term_base)
                != Key::canonical(MachineIntegerType::Int32, base)
        {
            return false;
        }
        let operation = if subtract {
            crate::kernel::machine_integer::Operation::Subtract
        } else {
            crate::kernel::machine_integer::Operation::Add
        };
        let base_value = base
            .observe(MachineIntegerType::Int32)
            .expect("int32 operand");
        let offset_value = IntegerTerm::constant(addend.into());
        let domain_known = |left, right| {
            crate::kernel::machine_integer::definedness::ordinary_bounds(
                MachineIntegerType::Int32,
                operation.exact(left, right),
            )
            .iter()
            .all(|bound| {
                let Proposition::ConditionIs(condition, true) = bound else {
                    unreachable!()
                };
                self.known_condition_value(condition) == Some(true)
            })
        };
        // Preserve the native add-domain rule's two written operand orders.
        if domain_known(base_value.clone(), offset_value.clone())
            || !subtract && domain_known(offset_value, base_value)
        {
            return true;
        }
        let interval = if subtract {
            self.signed_interval_past_exclusions_view(base)
        } else {
            self.signed_interval_view(base)
        };
        let Some((lower, upper)) = interval else {
            return false;
        };
        let offset = if subtract {
            -i64::from(addend)
        } else {
            i64::from(addend)
        };
        lower + offset >= i64::from(i32::MIN) && upper + offset <= i64::from(i32::MAX)
    }

    pub(super) fn decide_signed_constant_offset_order(
        &self,
        condition: &ConditionTerm,
    ) -> Option<bool> {
        use crate::kernel::machine_integer::comparison::comparison_view;
        let view = comparison_view(condition, true)?;
        if view.format != MachineIntegerType::Int32 {
            return None;
        }
        let strict = match view.relation {
            Relation::Less => true,
            Relation::LessEqual => false,
            _ => return None,
        };
        let [lower, upper] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        (self.constant_offset_is_proven(lower, upper, false, strict)
            || strict && self.constant_offset_is_proven(upper, lower, true, true))
        .then_some(true)
    }

    pub(super) fn is_bounded_by_base_before_nonnegative_offset_views(
        &self,
        lower: V<'_>,
        offset_term: V<'_>,
    ) -> bool {
        let Some((base, _)) = offset_term.int32_add_const_parts() else {
            return false;
        };
        self.exact_condition_value(
            &crate::kernel::machine_integer::comparison::condition_for_operand_views(
                MachineIntegerType::Int32,
                crate::kernel::CompareRelation::LessEqual,
                [lower, base],
            ),
        ) == Some(true)
            && self.constant_offset_is_proven(base, offset_term, false, false)
    }
}

impl SelectedFacts<'_> {
    /// Every order fact, for `solve`'s order search (`has_selected_order_path`,
    /// `selected_increment_preserves_order`). Fast walks read
    /// `OrderFactsByLower` instead.
    pub(in crate::kernel) fn condition_order_facts(&self) -> std::rc::Rc<Vec<OrderFact>> {
        // Ambient scope id when live, content id otherwise — the same
        // hash-once-per-distinct-fact-set policy `decide` pays at its entry.
        // A miss reads only the order facts (`order_condition_facts`), not
        // every condition fact, so a growing context of other facts does
        // not make each new context's collection grow with it.
        let memo_id = super::super::dag_memo_assumptions_id(self);
        if let Some(hit) = ORDER_FACTS_MEMO.with(|memo| memo.borrow().get(&memo_id).cloned()) {
            // One checkpoint keeps a run of memo hits responsive to the
            // cooperative deadline without rescanning the fact set.
            crate::kernel::assumptions::reasoning_interrupted();
            return hit;
        }
        let mut facts = Vec::new();
        let mut complete = true;
        for (condition, value) in self.order_condition_facts.scan_explicit_input() {
            if crate::kernel::assumptions::reasoning_interrupted() {
                complete = false;
                break;
            }
            if let Some(fact) = retained_order_fact(condition, *value) {
                facts.push(fact);
            }
        }
        #[cfg(debug_assertions)]
        if complete {
            crate::instrumentation::uncharged_debug_check(|| {
                let scanned = self
                    .condition_facts
                    .scan_for_upkeep()
                    .filter_map(|(condition, value)| retained_order_fact(condition, *value))
                    .collect::<Vec<_>>();
                assert_eq!(
                    facts, scanned,
                    "the order-fact index disagrees with the condition facts"
                );
            });
        }
        let facts = std::rc::Rc::new(facts);
        // A scan cut short by the deadline is not this fact set's collection;
        // only complete scans are shared.
        if complete {
            ORDER_FACTS_MEMO.with(|memo| {
                let mut memo = memo.borrow_mut();
                if memo.len() >= ORDER_FACTS_MEMO_LIMIT {
                    memo.clear();
                }
                memo.insert(memo_id, facts.clone());
            });
        }
        facts
    }
}

// These consumers need only a literal or one additive root, never a boxed
// expansion of a retained bound.

fn shared_signed_const_add(term: V<'_>, addend: u32) -> Option<MachineTerm> {
    let sum = (term.word32_constant()? as i32).checked_add(i32::try_from(addend).ok()?)?;
    Some(MachineTerm::constant(sum as u32))
}

fn shared_successor_of(term: V<'_>, right: V<'_>) -> bool {
    if let (V::Legacy(term), V::Legacy(right)) = (term, right) {
        return term.add_const_base(1).is_some_and(|base| base == *right);
    }
    let Some((format, crate::kernel::MachineBinaryOp::Add, [left, right_operand])) = term.binary()
    else {
        return false;
    };
    if format != MachineIntegerType::Int32 {
        return false;
    }
    use crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey as Key;
    let same = |operand| {
        Key::for_format(MachineIntegerType::Int32, operand)
            == Key::for_format(MachineIntegerType::Int32, right)
    };
    (right_operand.literal() == Some(MachineTerm::constant(1)) && same(left))
        || (left.literal() == Some(MachineTerm::constant(1)) && same(right_operand))
}

#[cfg(test)]
mod shared_bound_tests {
    #[test]
    fn shared_endpoint_bounds_keep_roots_and_contexts() {
        use super::*;
        use crate::kernel::{KernelTerm, KernelType, MachineBinaryOp, SharedMachineIntegerTerm};
        let _session = crate::kernel::VerificationSession::enter();
        for format in [MachineIntegerType::Int32, MachineIntegerType::UInt32] {
            let make = |id| {
                let variable = KernelTerm::variable(KernelType::C(format.c_type()), Variable(id));
                let root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [variable.clone(), variable],
                );
                SharedMachineIntegerTerm::from_shared(format, root).unwrap()
            };
            let left = make(994821);
            let right = make(994822);
            let comparison =
                |relation, a: &SharedMachineIntegerTerm, b: &SharedMachineIntegerTerm| {
                    NativeComparisonView {
                        format,
                        relation,
                        operands: [
                            ComparisonOperand::Observation(a.clone()),
                            ComparisonOperand::Observation(b.clone()),
                        ],
                    }
                    .integer_condition()
                };
            let parent = PureFactContext::new();
            assert!(!parent.has_upper_bound_below_views(left.operand_view(), right.operand_view()));
            let middle = make(994823);
            let child = parent
                .clone()
                .assume_condition(comparison(Relation::Less, &left, &middle), true)
                .assume_condition(comparison(Relation::LessEqual, &middle, &right), true);
            match format {
                MachineIntegerType::Int32 => {
                    assert!(
                        child
                            .has_upper_bound_below_views(left.operand_view(), right.operand_view())
                    );
                    assert!(
                        child
                            .has_lower_bound_above_views(right.operand_view(), left.operand_view())
                    );
                }
                MachineIntegerType::UInt32 => {
                    assert!(child.has_unsigned32_bound_between_views(
                        left.operand_view(),
                        right.operand_view(),
                        true
                    ));
                    assert!(!child.has_unsigned32_bound_between_views(
                        right.operand_view(),
                        left.operand_view(),
                        false
                    ));
                }
                _ => unreachable!(),
            }
            if format == MachineIntegerType::Int32 {
                assert!(child.has_exact_order_path_views(
                    left.operand_view(),
                    right.operand_view(),
                    true
                ));
                assert!(!child.has_exact_order_path_views(
                    right.operand_view(),
                    left.operand_view(),
                    false
                ));
                assert!(!parent.has_exact_order_path_views(
                    left.operand_view(),
                    right.operand_view(),
                    true
                ));
            }
            assert!(!left.has_boxed_operand());
            assert!(!right.has_boxed_operand());
            assert!(!middle.has_boxed_operand());
            assert!(!parent.has_upper_bound_below_views(left.operand_view(), right.operand_view()));
            assert!(!left.has_boxed_operand());
            assert!(!right.has_boxed_operand());
        }
    }

    #[test]
    fn shared_constant_comparisons_use_operand_classes_without_export() {
        use super::*;
        use crate::kernel::{KernelTerm, KernelType, MachineBinaryOp, SharedMachineIntegerTerm};
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let a = Variable(994811);
        let b = Variable(994812);
        let root = KernelTerm::machine_binary_shared(
            ty,
            MachineBinaryOp::Add,
            [
                KernelTerm::variable(KernelType::C(ty.c_type()), a),
                KernelTerm::variable(KernelType::C(ty.c_type()), b),
            ],
        );
        let operand = SharedMachineIntegerTerm::from_shared(ty, root).unwrap();
        let facts = PureFactContext::new()
            .assume_condition(
                ConditionTerm::equal(MachineTerm::Variable(a), MachineTerm::constant(1)),
                true,
            )
            .assume_condition(
                ConditionTerm::equal(MachineTerm::Variable(b), MachineTerm::constant(2)),
                true,
            );
        for (limit, expected) in [(4, true), (3, false)] {
            let query = ConditionTerm::integer_less_than(
                IntegerTerm::Machine(operand.clone()),
                IntegerTerm::constant(limit.into()),
            );
            assert_eq!(facts.decide(&query), Some(expected));
            assert!(!operand.has_boxed_operand());
        }
    }

    #[test]
    fn shared_offset_decisions_keep_operands_and_require_definedness() {
        use super::*;
        use crate::kernel::machine_integer::{Operation, definedness::ordinary_bounds};
        use crate::kernel::{
            KernelTerm, KernelType, MachineBinaryOp as Op, MachineIntegerType as Ty,
            SharedMachineIntegerTerm,
        };
        let _session = crate::kernel::VerificationSession::enter();
        let variable = Variable(994801);
        let root = KernelTerm::variable(KernelType::C(Ty::Int32.c_type()), variable);
        let base = SharedMachineIntegerTerm::from_shared(Ty::Int32, root.clone()).unwrap();
        let literal = crate::kernel::KernelTermImport::default()
            .machine_arithmetic(Ty::Int32, &MachineTerm::constant(1))
            .unwrap();
        for (op, operation) in [
            (Op::Add, Operation::Add),
            (Op::Subtract, Operation::Subtract),
        ] {
            let term = SharedMachineIntegerTerm::from_shared(
                Ty::Int32,
                KernelTerm::machine_binary_shared(Ty::Int32, op, [root.clone(), literal.clone()]),
            )
            .unwrap();
            let b = IntegerTerm::Machine(base.clone());
            let t = IntegerTerm::Machine(term.clone());
            let query = if op == Op::Add {
                ConditionTerm::integer_less_than(b.clone(), t)
            } else {
                ConditionTerm::integer_less_than(t, b.clone())
            };
            let parent = PureFactContext::new();
            assert_eq!(parent.decide_signed_constant_offset_order(&query), None);
            assert!(!term.has_boxed_operand());
            let exact = operation.exact(b, IntegerTerm::constant(1.into()));
            let [upper, lower] = ordinary_bounds(Ty::Int32, exact);
            let child = parent
                .clone()
                .assume_proposition(upper)
                .assume_proposition(lower);
            assert_eq!(child.decide(&query), Some(true));
            assert!(!term.has_boxed_operand());
            assert_eq!(parent.decide_signed_constant_offset_order(&query), None);
            if op == Op::Add {
                let reversed = Operation::Add.exact(
                    IntegerTerm::constant(1.into()),
                    IntegerTerm::Machine(base.clone()),
                );
                let [upper, lower] = ordinary_bounds(Ty::Int32, reversed);
                let reversed = parent
                    .clone()
                    .assume_proposition(upper)
                    .assume_proposition(lower);
                assert_eq!(reversed.decide(&query), Some(true));
                assert!(!term.has_boxed_operand());
            }
            if op == Op::Subtract {
                let excluded = parent.clone().assume_condition(
                    ConditionTerm::equal(
                        MachineTerm::Variable(variable),
                        MachineTerm::constant(i32::MIN as u32),
                    ),
                    false,
                );
                assert_eq!(excluded.decide(&query), Some(true));
                assert!(!term.has_boxed_operand());
            }
            let endpoint = if op == Op::Add { i32::MAX } else { i32::MIN };
            let safe = parent.clone().assume_condition(
                if op == Op::Add {
                    ConditionTerm::signed_less_than(
                        MachineTerm::Variable(variable),
                        MachineTerm::constant(endpoint as u32),
                    )
                } else {
                    ConditionTerm::signed_greater_than(
                        MachineTerm::Variable(variable),
                        MachineTerm::constant(endpoint as u32),
                    )
                },
                true,
            );
            assert_eq!(safe.decide(&query), Some(true));
            assert!(!term.has_boxed_operand());
            let overflowing = parent.assume_condition(
                ConditionTerm::equal(
                    MachineTerm::Variable(variable),
                    MachineTerm::constant(endpoint as u32),
                ),
                true,
            );
            assert_eq!(
                overflowing.decide_signed_constant_offset_order(&query),
                None
            );
            assert!(!term.has_boxed_operand());
        }
    }

    use super::*;
    use crate::kernel::{KernelTerm, KernelType, MachineBinaryOp, Variable};

    #[test]
    fn shared_bounds_keep_strictness_and_require_the_second_premise() {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let root = KernelTerm::machine_binary_shared(
            ty,
            MachineBinaryOp::Add,
            [
                KernelTerm::variable(KernelType::C(ty.c_type()), Variable(994101)),
                KernelTerm::variable(KernelType::C(ty.c_type()), Variable(994102)),
            ],
        );
        let operand = SharedMachineIntegerTerm::from_shared(ty, root).unwrap();
        let x = MachineTerm::Variable(Variable(994103));
        let y = MachineTerm::Variable(Variable(994104));
        let observe = |term| IntegerTerm::from_machine(ty, term).unwrap();
        let first = ConditionTerm::integer_less_equal(
            observe(x.clone()),
            IntegerTerm::Machine(operand.clone()),
        );
        let second = ConditionTerm::integer_less_equal(
            IntegerTerm::Machine(operand.clone()),
            observe(y.clone()),
        );
        let parent = PureFactContext::new().assume_condition(first, true);
        let facts = parent.clone().assume_condition(second, true);
        assert!(facts.has_upper_bound_at_or_below(&x, &y));
        assert!(!operand.has_boxed_operand());
        // Unresolved queries still reach the general decision dispatcher's
        // native compatibility conversion. Preserve its refusal behavior;
        // migrating that boundary is separate from retaining selected bounds.
        assert!(!facts.has_upper_bound_below(&x, &y));
        assert!(!parent.has_upper_bound_at_or_below(&x, &y));
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/assumptions/condition_reasoning/bounds.rs");
}

#[cfg(test)]
mod shared_offset_bound_consumers {
    use super::*;
    use crate::kernel::{KernelTerm, KernelTermImport, MachineBinaryOp};

    #[test]
    fn shared_shifted_bounds_require_domains_and_keep_strictness() {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let written = MachineTerm::Binary {
            format,
            op: MachineBinaryOp::Add,
            left: MachineTerm::Variable(Variable(998701)).into(),
            right: MachineTerm::Variable(Variable(998702)).into(),
        };
        let root = KernelTermImport::default()
            .machine_arithmetic(format, &written)
            .unwrap();
        let two = KernelTermImport::default()
            .machine_arithmetic(format, &MachineTerm::constant(2))
            .unwrap();
        let shifted = |op| {
            SharedMachineIntegerTerm::from_shared(
                format,
                KernelTerm::machine_binary_shared(format, op, [root.clone(), two.clone()]),
            )
            .unwrap()
        };
        let add = shifted(MachineBinaryOp::Add);
        let sub = shifted(MachineBinaryOp::Subtract);
        let parent = PureFactContext::new();
        let upper_only = parent.clone().assume_condition(
            ConditionTerm::signed_less_equal(written.clone(), MachineTerm::constant(10)),
            true,
        );
        let bounded = upper_only.clone().assume_condition(
            ConditionTerm::signed_greater_equal(written, MachineTerm::constant(0)),
            true,
        );
        let eight = MachineTerm::constant(8);
        let twelve = MachineTerm::constant(12);
        let two = MachineTerm::constant(2);
        let negative_two = MachineTerm::constant((-2i32) as u32);
        assert!(
            bounded.has_add_const_upper_bound_at_or_below_views(
                add.operand_view(),
                V::Legacy(&twelve)
            )
        );
        assert!(
            !bounded.has_add_const_upper_bound_below_views(add.operand_view(), V::Legacy(&twelve))
        );
        assert!(
            bounded
                .has_add_const_lower_bound_at_or_above_views(add.operand_view(), V::Legacy(&two))
        );
        assert!(
            !bounded.has_add_const_lower_bound_above_views(add.operand_view(), V::Legacy(&two))
        );
        assert!(bounded.has_subtract_const_upper_bound_views(
            sub.operand_view(),
            V::Legacy(&eight),
            false
        ));
        assert!(!bounded.has_subtract_const_upper_bound_views(
            sub.operand_view(),
            V::Legacy(&eight),
            true
        ));
        assert!(bounded.has_subtract_const_lower_bound_views(
            sub.operand_view(),
            V::Legacy(&negative_two),
            false
        ));
        assert!(!bounded.has_subtract_const_lower_bound_views(
            sub.operand_view(),
            V::Legacy(&negative_two),
            true
        ));
        assert!(!upper_only.has_subtract_const_upper_bound_views(
            sub.operand_view(),
            V::Legacy(&eight),
            false
        ));
        assert!(
            !parent.has_add_const_upper_bound_at_or_below_views(
                add.operand_view(),
                V::Legacy(&twelve)
            )
        );
        assert!(!add.has_boxed_operand());
        assert!(!sub.has_boxed_operand());
    }
}

#[cfg(test)]
mod nested_search_tests {
    use super::*;

    #[test]
    fn refused_nested_bound_search_keeps_the_outer_guard() {
        let outer = NestedBoundSearch::enter().expect("outer search");
        assert!(NestedBoundSearch::enter().is_none());
        assert!(NestedBoundSearch::enter().is_none());
        drop(outer);
        assert!(NestedBoundSearch::enter().is_some());
    }
}
