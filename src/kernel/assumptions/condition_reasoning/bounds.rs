use super::*;
use crate::kernel::machine_integer::{
    Relation,
    comparison::{ComparisonOperand, NativeComparisonView},
};
use crate::kernel::{MachineOperandView as V, SharedMachineIntegerTerm};

/// One collected order fact: `left (<|<=) right` with its strictness.
pub(in crate::kernel) type OrderFact = (Bitvector32Term, Bitvector32Term, bool);

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
        lower: Bitvector32Term,
        upper: Bitvector32Term,
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
        (!BOUND_SEARCH_DECIDING.with(|deciding| deciding.replace(true))).then_some(Self)
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
        order_facts: &mut Vec<(Bitvector32Term, Bitvector32Term, bool)>,
    ) {
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                if let Some(order_fact) = condition_as_order_fact(condition, *value) {
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
        order_facts: &mut Vec<(Bitvector32Term, Bitvector32Term, bool)>,
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
        order_facts: &mut Vec<(Bitvector32Term, Bitvector32Term, bool)>,
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
    /// [`Self::bound_proves_order_in`] judges, so the search never recurses
    /// along a chain of bounds.
    pub(in crate::kernel) fn has_unsigned32_bound_between(
        &self,
        lower: &Bitvector32Term,
        upper: &Bitvector32Term,
        strict: bool,
    ) -> bool {
        let kind = OrderKind::Unsigned32;
        self.bounds_for_search(kind, lower, true)
            .into_iter()
            .any(|(bound, bound_strict)| {
                self.bound_proves_order_views(
                    kind,
                    bound.operand_view(),
                    V::Legacy(upper),
                    strict && !bound_strict,
                )
            })
            || self.bounds_for_search(kind, upper, false).into_iter().any(
                |(bound, bound_strict)| {
                    self.bound_proves_order_views(
                        kind,
                        V::Legacy(lower),
                        bound.operand_view(),
                        strict && !bound_strict,
                    )
                },
            )
    }

    /// Whether a recorded upper bound of `left` lies at or below `right`
    /// (below it when the bound is not strict), so `left < right`.
    pub(in crate::kernel) fn has_upper_bound_below(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        self.upper_bounds_for_search(left)
            .into_iter()
            .any(|(upper, strict)| {
                self.bound_proves_order_views(
                    OrderKind::Signed32,
                    upper.operand_view(),
                    V::Legacy(right),
                    !strict,
                )
            })
    }

    /// Whether a recorded upper bound of `left` lies at or below `right`, so
    /// `left <= right`.
    pub(in crate::kernel) fn has_upper_bound_at_or_below(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        self.upper_bounds_for_search(left)
            .into_iter()
            .any(|(upper, _)| {
                self.bound_proves_order_views(
                    OrderKind::Signed32,
                    upper.operand_view(),
                    V::Legacy(right),
                    false,
                )
            })
    }

    /// `left < right` from a recorded `left < right + 1` and a recorded
    /// `left != right`.
    pub(in crate::kernel) fn has_successor_upper_bound_below(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        self.upper_bounds_for_search(left)
            .into_iter()
            .any(|(upper, strict)| {
                strict
                    && shared_successor_of(upper.operand_view(), right)
                    && self.has_condition_fact(
                        ConditionTerm::equal(left.clone(), right.clone()),
                        false,
                    )
            })
    }

    pub(in crate::kernel) fn has_add_const_upper_bound_below(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let Some((base, addend)) = left.add_const_parts() else {
            return false;
        };
        if self.decide(&ConditionTerm::signed_add_overflows(
            base.clone(),
            Bitvector32Term::Constant(addend),
        )) != Some(false)
        {
            return false;
        }
        // `base < upper` gives `left < upper + addend`, so `upper + addend
        // <= right` is enough; `base <= upper` needs `upper + addend < right`.
        self.upper_bounds_for_search(&base)
            .into_iter()
            .any(|(upper, strict)| {
                shared_signed_const_add(upper.operand_view(), addend)
                    .is_some_and(|upper| self.bound_proves_order(&upper, right, !strict))
            })
    }

    pub(in crate::kernel) fn has_add_const_upper_bound_at_or_below(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let Some((base, addend)) = left.add_const_parts() else {
            return false;
        };
        if self.decide(&ConditionTerm::signed_add_overflows(
            base.clone(),
            Bitvector32Term::Constant(addend),
        )) != Some(false)
        {
            return false;
        }
        self.upper_bounds_for_search(&base)
            .into_iter()
            .any(|(upper, _)| {
                shared_signed_const_add(upper.operand_view(), addend)
                    .is_some_and(|upper| self.bound_proves_order(&upper, right, false))
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
    pub(in crate::kernel) fn has_subtract_const_upper_bound(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        strict_goal: bool,
    ) -> bool {
        let Some((base, subtrahend)) = left.subtract_const_parts() else {
            return false;
        };
        let Ok(subtrahend_value) = i32::try_from(subtrahend) else {
            return false;
        };
        if subtrahend_value <= 0 {
            return false;
        }
        let canonical = crate::kernel::eval::canonical_term(&base);
        let keys = if canonical == base {
            vec![base.clone()]
        } else {
            vec![base.clone(), canonical]
        };
        let mut upper_bounds = Vec::new();
        for key in keys {
            let Some(entries) = self.signed_order_bounds.get(&key) else {
                continue;
            };
            for (_, other, strict, own_is_lower) in entries.operand_keys() {
                if own_is_lower
                    && let Some(upper) = other.word32_constant()
                    && !upper_bounds.contains(&(upper, strict))
                {
                    crate::instrumentation::record_deterministic_work(1);
                    upper_bounds.push((upper, strict));
                }
            }
        }
        if upper_bounds.is_empty()
            || self.decide(&ConditionTerm::signed_subtract_overflows(
                base.clone(),
                Bitvector32Term::Constant(subtrahend),
            )) != Some(false)
        {
            return false;
        }
        upper_bounds.into_iter().any(|(upper, strict_fact)| {
            let Some(shifted) = (upper as i32).checked_sub(subtrahend_value) else {
                return false;
            };
            let shifted = Bitvector32Term::Constant(shifted as u32);
            // `base < upper` gives `base - c < upper - c`; `base <= upper`
            // gives `base - c <= upper - c`.
            let goal = if strict_goal && !strict_fact {
                ConditionTerm::signed_less_than(shifted, right.clone())
            } else {
                ConditionTerm::signed_less_equal(shifted, right.clone())
            };
            self.decide(&goal) == Some(true)
        })
    }

    /// `bound <= base - c` (or `<` when `strict_goal`) from a recorded
    /// constant lower bound `lower <= base` (or `lower < base`) with
    /// `bound <= lower - c` (resp. `<`). `lower - c` is computed without
    /// wrapping, and `base >= lower` then keeps `base - c` from wrapping, so
    /// no separate underflow decision is needed.
    pub(in crate::kernel) fn has_subtract_const_lower_bound(
        &self,
        term: &Bitvector32Term,
        bound: &Bitvector32Term,
        strict_goal: bool,
    ) -> bool {
        let Some((base, subtrahend)) = term.subtract_const_parts() else {
            return false;
        };
        let Ok(subtrahend_value) = i32::try_from(subtrahend) else {
            return false;
        };
        if subtrahend_value <= 0 {
            return false;
        }
        let canonical = crate::kernel::eval::canonical_term(&base);
        let keys = if canonical == base {
            vec![base.clone()]
        } else {
            vec![base.clone(), canonical]
        };
        let mut lower_bounds = Vec::new();
        for key in keys {
            let Some(entries) = self.signed_order_bounds.get(&key) else {
                continue;
            };
            for (_, other, strict, own_is_lower) in entries.operand_keys() {
                if !own_is_lower
                    && let Some(lower) = other.word32_constant()
                    && !lower_bounds.contains(&(lower, strict))
                {
                    crate::instrumentation::record_deterministic_work(1);
                    lower_bounds.push((lower, strict));
                }
            }
        }
        lower_bounds.into_iter().any(|(lower, strict_fact)| {
            let Some(shifted) = (lower as i32).checked_sub(subtrahend_value) else {
                return false;
            };
            let shifted = Bitvector32Term::Constant(shifted as u32);
            let goal = if strict_goal && !strict_fact {
                ConditionTerm::signed_less_than(bound.clone(), shifted)
            } else {
                ConditionTerm::signed_less_equal(bound.clone(), shifted)
            };
            self.decide(&goal) == Some(true)
        })
    }

    pub(in crate::kernel) fn subtract_same_const_order_fact(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        strict: bool,
    ) -> bool {
        let Some((left_base, left_const)) = left.subtract_const_parts() else {
            return false;
        };
        let Some((right_base, right_const)) = right.subtract_const_parts() else {
            return false;
        };
        if left_const != right_const {
            return false;
        }
        // `base - const` wraps; an order between the bases only carries to
        // the subtracted terms when neither subtraction signed underflows
        // (otherwise `a < b` would prove `a - 1 < b - 1`, false at
        // a = INT_MIN, b = INT_MIN + 1).
        if self.decide(&ConditionTerm::signed_subtract_overflows(
            left_base.clone(),
            Bitvector32Term::Constant(left_const),
        )) != Some(false)
            || self.decide(&ConditionTerm::signed_subtract_overflows(
                right_base.clone(),
                Bitvector32Term::Constant(right_const),
            )) != Some(false)
        {
            return false;
        }

        if strict {
            self.has_condition_fact(
                ConditionTerm::signed_less_than(left_base.clone(), right_base.clone()),
                true,
            ) || self.has_condition_fact(
                ConditionTerm::signed_greater_than(right_base, left_base),
                true,
            )
        } else {
            self.has_condition_fact(
                ConditionTerm::signed_less_equal(left_base.clone(), right_base.clone()),
                true,
            ) || self.has_condition_fact(
                ConditionTerm::signed_greater_equal(right_base, left_base),
                true,
            )
        }
    }

    /// The lower bounds of `term` a lower-bound search may use, as
    /// `(lower, strict)` for each true order fact `lower < term` (strict) or
    /// `lower <= term`, in any of the written shapes (`<`, `<=`, `>`, `>=`,
    /// or a refuted converse).
    ///
    /// Every signed-order fact is indexed at both endpoints, under the term
    /// it wrote and under that term's canonical form
    /// (`PureFactContext::signed_order_bounds`), so the recorded bounds cost
    /// only the entries at `term`. A fact whose bounded endpoint is only
    /// provably equal to `term` (one load read at two snapshots, say) is not
    /// read: that would compare `term` with every order fact. A proof states
    /// the equality, or the bound at `term`'s own spelling.
    pub(super) fn lower_bounds_for_search(
        &self,
        term: &Bitvector32Term,
    ) -> Vec<(SharedMachineIntegerTerm, bool)> {
        self.bounds_for_search(OrderKind::Signed32, term, false)
    }

    /// The upper bounds of `term` as `(upper, strict)` for each true order
    /// fact `term < upper` (strict) or `term <= upper`, read from the
    /// endpoint index like [`Self::lower_bounds_for_search`].
    pub(super) fn upper_bounds_for_search(
        &self,
        term: &Bitvector32Term,
    ) -> Vec<(SharedMachineIntegerTerm, bool)> {
        self.bounds_for_search(OrderKind::Signed32, term, true)
    }

    /// The bounds of `term` in the order of `kind`, upper bounds when
    /// `upper` and lower bounds otherwise, from that order's endpoint index
    /// (`signed_order_bounds`, `uint32_order_bounds`) at `term` and its
    /// canonical form.
    pub(super) fn bounds_for_search(
        &self,
        kind: OrderKind,
        term: &Bitvector32Term,
        upper: bool,
    ) -> Vec<(SharedMachineIntegerTerm, bool)> {
        let index = match kind {
            OrderKind::Signed32 => &self.signed_order_bounds,
            OrderKind::Unsigned32 => &self.uint32_order_bounds,
        };
        let canonical = crate::kernel::eval::canonical_term(term);
        let keys = if canonical == *term {
            vec![canonical]
        } else {
            vec![term.clone(), canonical]
        };
        let mut bounds = Vec::new();
        for key in keys {
            let Some(entries) = index.get(&key) else {
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
    fn bound_proves_order(
        &self,
        lower: &Bitvector32Term,
        upper: &Bitvector32Term,
        strict: bool,
    ) -> bool {
        self.bound_proves_order_in(OrderKind::Signed32, lower, upper, strict)
    }

    /// [`Self::bound_proves_order`] in the order of `kind`.
    pub(super) fn bound_proves_order_in(
        &self,
        kind: OrderKind,
        lower: &Bitvector32Term,
        upper: &Bitvector32Term,
        strict: bool,
    ) -> bool {
        self.bound_proves_order_views(kind, V::Legacy(lower), V::Legacy(upper), strict)
    }

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
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        self.lower_bounds_for_search(left)
            .into_iter()
            .any(|(lower, strict)| {
                // `lower < left` and `lower >= right`, or `lower <= left` and
                // `lower > right`, give `left > right`.
                self.bound_proves_order_views(
                    OrderKind::Signed32,
                    V::Legacy(right),
                    lower.operand_view(),
                    !strict,
                )
            })
    }

    /// Whether a recorded lower bound of `left` lies at or above `right`, so
    /// `left >= right`.
    pub(in crate::kernel) fn has_lower_bound_at_or_above(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        self.lower_bounds_for_search(left)
            .into_iter()
            .any(|(lower, _)| {
                self.bound_proves_order_views(
                    OrderKind::Signed32,
                    V::Legacy(right),
                    lower.operand_view(),
                    false,
                )
            })
    }

    pub(in crate::kernel) fn has_add_const_lower_bound_above(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let Some((base, addend)) = left.add_const_parts() else {
            return false;
        };
        // `base + addend` wraps in two's complement, so a bound on `base`
        // only carries to `base + addend` when that sum does not signed
        // overflow. Without this guard `x >= 0` would wrongly prove
        // `x + 1 > 0` (false at x = INT_MAX). See positive_offset_is_proven_above.
        if self.decide(&ConditionTerm::signed_add_overflows(
            base.clone(),
            Bitvector32Term::Constant(addend),
        )) != Some(false)
        {
            return false;
        }
        // `lower < base` gives `lower + addend < left`, so `right <= lower +
        // addend` is enough; `lower <= base` needs `right < lower + addend`.
        self.lower_bounds_for_search(&base)
            .into_iter()
            .any(|(lower, strict)| {
                shared_signed_const_add(lower.operand_view(), addend)
                    .is_some_and(|lower| self.bound_proves_order(right, &lower, !strict))
            })
    }

    pub(in crate::kernel) fn has_add_const_lower_bound_at_or_above(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let Some((base, addend)) = left.add_const_parts() else {
            return false;
        };
        // `base + addend` wraps; only carry the bound when it does not
        // signed overflow (otherwise `x >= 0` would prove `x + 1 >= 1`,
        // false at x = INT_MAX).
        if self.decide(&ConditionTerm::signed_add_overflows(
            base.clone(),
            Bitvector32Term::Constant(addend),
        )) != Some(false)
        {
            return false;
        }
        self.lower_bounds_for_search(&base)
            .into_iter()
            .any(|(lower, _)| {
                shared_signed_const_add(lower.operand_view(), addend)
                    .is_some_and(|lower| self.bound_proves_order(right, &lower, false))
            })
    }

    /// The existing constant-offset order rule, over either operand representation.
    /// Match only the operation root before reading the base's range or domain.
    fn constant_offset_is_proven(
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
            (_, Some(Bitvector32Term::Constant(n))) => (a, n),
            (Some(Bitvector32Term::Constant(n)), _) if !subtract => (b, n),
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

    pub(in crate::kernel) fn positive_offset_is_proven_above(
        &self,
        base: &Bitvector32Term,
        term: &Bitvector32Term,
    ) -> bool {
        self.constant_offset_is_proven(V::Legacy(base), V::Legacy(term), false, true)
    }

    pub(in crate::kernel) fn positive_subtraction_is_proven_below(
        &self,
        term: &Bitvector32Term,
        base: &Bitvector32Term,
    ) -> bool {
        self.constant_offset_is_proven(V::Legacy(base), V::Legacy(term), true, true)
    }

    pub(in crate::kernel) fn nonnegative_offset_is_proven_at_or_above(
        &self,
        base: &Bitvector32Term,
        term: &Bitvector32Term,
    ) -> bool {
        self.constant_offset_is_proven(V::Legacy(base), V::Legacy(term), false, false)
    }

    pub(in crate::kernel) fn is_bounded_by_base_before_nonnegative_offset(
        &self,
        lower: &Bitvector32Term,
        offset_term: &Bitvector32Term,
    ) -> bool {
        let Some((base, _)) = offset_term.add_const_parts() else {
            return false;
        };
        self.exact_condition_value(&ConditionTerm::signed_less_equal(
            lower.clone(),
            base.clone(),
        )) == Some(true)
            && self.nonnegative_offset_is_proven_at_or_above(&base, offset_term)
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
            if let Some(fact) = condition_as_order_fact(condition, *value) {
                facts.push(fact);
            }
        }
        #[cfg(debug_assertions)]
        if complete {
            crate::instrumentation::uncharged_debug_check(|| {
                let scanned = self
                    .condition_facts
                    .scan_for_upkeep()
                    .filter_map(|(condition, value)| condition_as_order_fact(condition, *value))
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
fn shared_signed_const_add(term: V<'_>, addend: u32) -> Option<Bitvector32Term> {
    let sum = (term.word32_constant()? as i32).checked_add(i32::try_from(addend).ok()?)?;
    Some(Bitvector32Term::Constant(sum as u32))
}

fn shared_successor_of(term: V<'_>, right: &Bitvector32Term) -> bool {
    if let V::Legacy(term) = term {
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
            == Key::for_format(MachineIntegerType::Int32, V::Legacy(right))
    };
    (right_operand.literal() == Some(Bitvector32Term::Constant(1)) && same(left))
        || (left.literal() == Some(Bitvector32Term::Constant(1)) && same(right_operand))
}

#[cfg(test)]
mod shared_bound_tests {
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
                ConditionTerm::equal(Bitvector32Term::Variable(a), Bitvector32Term::Constant(1)),
                true,
            )
            .assume_condition(
                ConditionTerm::equal(Bitvector32Term::Variable(b), Bitvector32Term::Constant(2)),
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
            .machine_arithmetic(Ty::Int32, &Bitvector32Term::Constant(1))
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
                        Bitvector32Term::Variable(variable),
                        Bitvector32Term::Constant(i32::MIN as u32),
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
                        Bitvector32Term::Variable(variable),
                        Bitvector32Term::Constant(endpoint as u32),
                    )
                } else {
                    ConditionTerm::signed_greater_than(
                        Bitvector32Term::Variable(variable),
                        Bitvector32Term::Constant(endpoint as u32),
                    )
                },
                true,
            );
            assert_eq!(safe.decide(&query), Some(true));
            assert!(!term.has_boxed_operand());
            let overflowing = parent.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(variable),
                    Bitvector32Term::Constant(endpoint as u32),
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
        let x = Bitvector32Term::Variable(Variable(994103));
        let y = Bitvector32Term::Variable(Variable(994104));
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
