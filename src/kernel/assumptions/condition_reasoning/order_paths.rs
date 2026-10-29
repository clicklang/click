use super::*;
use crate::kernel::binary_term;
use crate::kernel::{CompareRelation, MachineIntegerType};

impl PureFactContext {
    /// Follow only written signed-order edges filed under the selected
    /// endpoint. No equality transport, arithmetic search or memory-history
    /// query participates. Retain provenance only for the successful path.
    pub(in crate::kernel) fn proves_recorded_signed_order(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        require_strict: bool,
    ) -> bool {
        let start = (left.clone(), false);
        let mut parents = BTreeMap::from([(start.clone(), None)]);
        let mut stack = vec![start];
        while let Some(state) = stack.pop() {
            let (current, strict_so_far) = &state;
            crate::instrumentation::record_deterministic_work(1);
            if crate::kernel::assumptions::reasoning_interrupted() {
                return false;
            }
            if current == right && (!require_strict || *strict_so_far) {
                let mut cursor = &state;
                while let Some(Some((previous, premise))) = parents.get(cursor) {
                    record_implicit_reasoning_provenance(self, premise);
                    cursor = previous;
                }
                return true;
            }
            let Some(bounds) = self.signed_order_bounds.get(current) else {
                continue;
            };
            for ((lower, upper, strict, outgoing), _) in bounds.iter() {
                crate::instrumentation::record_deterministic_work(1);
                if !outgoing || lower != current {
                    continue;
                }
                let next = (upper.clone(), *strict_so_far || *strict);
                if parents.contains_key(&next) {
                    continue;
                }
                // The index normalizes direction and polarity. Recover the
                // exact written premise before retaining a successful path.
                let positive = if *strict {
                    ConditionTerm::signed_less_than(lower.clone(), upper.clone())
                } else {
                    ConditionTerm::signed_less_equal(lower.clone(), upper.clone())
                };
                let reversed = if *strict {
                    ConditionTerm::signed_greater_than(upper.clone(), lower.clone())
                } else {
                    ConditionTerm::signed_greater_equal(upper.clone(), lower.clone())
                };
                let negative = if *strict {
                    ConditionTerm::signed_less_equal(upper.clone(), lower.clone())
                } else {
                    ConditionTerm::signed_less_than(upper.clone(), lower.clone())
                };
                let negative_reversed = if *strict {
                    ConditionTerm::signed_greater_equal(lower.clone(), upper.clone())
                } else {
                    ConditionTerm::signed_greater_than(lower.clone(), upper.clone())
                };
                let premise = [
                    (positive, true),
                    (reversed, true),
                    (negative, false),
                    (negative_reversed, false),
                ]
                .into_iter()
                .find(|(condition, value)| self.condition_facts.get(condition) == Some(value))
                .map(|(condition, value)| Proposition::ConditionIs(condition, value));
                if let Some(premise) = premise {
                    parents.insert(next.clone(), Some((state.clone(), premise)));
                    stack.push(next);
                }
            }
        }
        false
    }

    #[cfg(test)]
    /// Whether one recorded strict order fact separates `left` from `right`
    /// directly (`left < right` or `right < left`, under either term or its
    /// canonical alias). This is an indexed lookup only — no derivation, no
    /// fuel — so an assumption-free walk such as memory-derivation naming can
    /// refute an offset equality from a recorded bound without reasoning.
    pub(in crate::kernel) fn direct_strict_order_recorded(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let separated = |endpoint: &Bitvector32Term| {
            self.signed_order_bounds
                .get(endpoint)
                .is_some_and(|bounds| {
                    bounds.iter().any(|((lower, upper, strict, _), _)| {
                        *strict
                            && ((lower == left && upper == right)
                                || (lower == right && upper == left))
                    })
                })
        };
        separated(left)
            || separated(right)
            || separated(&crate::kernel::eval::canonical_term(left))
            || separated(&crate::kernel::eval::canonical_term(right))
    }

    pub(in crate::kernel) fn decide_from_order_facts(
        &self,
        condition: &ConditionTerm,
    ) -> Option<bool> {
        if let Some(result) = self.decide_from_variable_chain(condition) {
            return Some(result);
        }
        if let Some((term, bound, _)) = unsigned_upper_bound_below_sign_bit(condition, true)
            && let Some(value) = self.decide_unsigned_upper_bound_by_signed_order(term, bound)
        {
            return Some(value);
        }
        if let Some(value) = self.decide_from_order_rules(condition) {
            return Some(value);
        }
        // Successor rules the memory-resolution prover reads the same way
        // (`proves_order_condition_for_memory_resolution`), after the direct
        // rules have missed. Each asks one smaller strict question.
        let (lower, upper, strict) = condition_as_order_fact(condition, true)?;
        if let Some((below, above)) = successor_bound_as_strict_order(&lower, &upper, strict)
            && self.decide(&ConditionTerm::signed_less_than(below, above)) == Some(true)
        {
            return Some(true);
        }
        if let Some(((below, above, reduced_strict), base)) =
            constant_below_successor_as_order(&lower, &upper, strict)
            && self.decide(&order_condition(below, above, reduced_strict)) == Some(true)
            && self.decide(&ConditionTerm::signed_less_than(
                base,
                Bitvector32Term::Constant(i32::MAX as u32),
            )) == Some(true)
        {
            return Some(true);
        }
        self.signed_bound_from_unsigned_order(&lower, &upper, strict)
            .then_some(true)
    }

    /// Whether a signed bound between a plain variable `t` and a constant
    /// follows from a `uint32` order chain on `t`, which the difference graph
    /// composes in its unsigned domain (`t <u n`, `n <=u 4` gives `t <u 4`):
    ///
    /// * `c <= t` for `c <= 0` (or `c < t` for `c < 0`) holds when
    ///   `t <=u INT_MAX`: the sign bit of `t` is clear, so `0 <= t`.
    /// * `t <= c` for `c >= 0` (or `t < c` for `c > 0`) holds when
    ///   `t <=u c` (or `t <u c`): `t` lies in `0..=c` (or `0..c`), where the
    ///   unsigned and signed readings agree.
    ///
    /// The chain is walked over unsigned facts alone: a chain mixing
    /// `t <u n` with a signed `n < 4` does not compose here. A wrapped bound
    /// (`t <u n - 1u` with `n` possibly zero) is a different value from `n`.
    /// One difference-graph query from `t`
    /// ([`Self::difference_graph_proves`]).
    fn signed_bound_from_unsigned_order(
        &self,
        lower: &Bitvector32Term,
        upper: &Bitvector32Term,
        strict: bool,
    ) -> bool {
        let (term, target, walk_strict) = match (
            signed_bitvector_constant(lower),
            signed_bitvector_constant(upper),
        ) {
            (Some(bound), None) if (if strict { bound < 0 } else { bound <= 0 }) => {
                (upper, i32::MAX as u32, false)
            }
            (None, Some(bound)) if (if strict { bound > 0 } else { bound >= 0 }) => {
                (lower, bound as u32, strict)
            }
            _ => return false,
        };
        if !matches!(term, Bitvector32Term::Variable(variable)
            if !crate::kernel::eval::is_load_variable(variable))
        {
            return false;
        }
        // A walk needs an unsigned upper bound on `t`. Asked by key first,
        // so a signed question about a variable no unsigned bound names
        // costs one lookup, not the filing of the fact set the walk reads.
        let has_unsigned_bound = self
            .uint32_order_bounds
            .get(&crate::kernel::eval::canonical_term(term))
            .is_some_and(|bounds| bounds.iter().any(|((_, _, _, below), _)| *below));
        let target = Bitvector32Term::Constant(target);
        has_unsigned_bound
            && self.difference_graph_proves(&if walk_strict {
                ConditionTerm::unsigned_less_than(term.clone(), target)
            } else {
                ConditionTerm::unsigned_less_equal(term.clone(), target)
            })
    }

    fn decide_from_order_rules(&self, condition: &ConditionTerm) -> Option<bool> {
        match condition {
            ConditionTerm::PointerEqual(left, right) if left == right => Some(true),
            ConditionTerm::PointerEqual(left, right) => {
                if self.pointers_known_equal(left, right) {
                    Some(true)
                } else if left.block == right.block {
                    self.decide_from_order_rules(&ConditionTerm::pointer_offset_equal(
                        left.offset.clone(),
                        right.offset.clone(),
                    ))
                } else {
                    left.blocks_proven_distinct(right).then_some(false)
                }
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left,
                right,
            } => {
                if self.uint64_values_known_equal(left, right) {
                    return Some(true);
                }
                if let Some(pointer_condition) =
                    ConditionTerm::address_equality_as_pointer_equality(left, right)
                {
                    return self.decide(&pointer_condition);
                }
                if let Some((pointer, alignment)) = condition.as_pointer_alignment() {
                    return self.decide_pointer_alignment(pointer, alignment);
                }
                self.decide_uint64_equality_extras(left, right)
            }
            ConditionTerm::PointerOffsetEqual(left, right) if left == right => Some(true),
            ConditionTerm::PointerOffsetEqual(left, right) => {
                if pointer_offsets_proven_equal_for_memory_resolution(left, right, self) {
                    return Some(true);
                }
                match (left.as_ref().as_const(), right.as_ref().as_const()) {
                    (Some(left), Some(right)) => Some(left == right),
                    _ => {
                        // Addends both offsets share cancel exactly over the
                        // integers, so only the remainders are compared; a
                        // shared symbolic base offset then no longer blocks
                        // an exact decision about the indices.
                        let (left, right) = cancel_common_offset_addends(left, right);
                        if let (Some(left), Some(right)) = (left.as_const(), right.as_const()) {
                            return Some(left == right);
                        }
                        let (left, right) = (&left, &right);
                        // One scaled index against a constant is exactly a
                        // question about the index: `x * 8 + 4 == 12` is
                        // `x == 1`, at any stride.
                        if let Some((index, element)) =
                            single_scaled_index_equal_to_constant(left, right)
                                .or_else(|| single_scaled_index_equal_to_constant(right, left))
                        {
                            return self.decide(&ConditionTerm::equal(
                                index.clone(),
                                Bitvector32Term::Constant(element as u32),
                            ));
                        }
                        let left_index = int32_element_index_from_offset(left);
                        let right_index = int32_element_index_from_offset(right);
                        match (left_index, right_index) {
                            (Some(left_index), Some(right_index)) => exact_or_unequal(
                                self.decide(&ConditionTerm::equal(left_index, right_index)),
                                self.rebuilt_offset_is_exact(left, 4, false)
                                    && self.rebuilt_offset_is_exact(right, 4, false),
                            ),
                            _ => {
                                let left_bytes = byte_offset_from_pointer_offset(left);
                                let right_bytes = byte_offset_from_pointer_offset(right);
                                match (left_bytes, right_bytes) {
                                    (Some(left_bytes), Some(right_bytes)) => exact_or_unequal(
                                        self.decide(&ConditionTerm::equal(left_bytes, right_bytes)),
                                        self.rebuilt_offset_is_exact(left, 4, true)
                                            && self.rebuilt_offset_is_exact(right, 4, true),
                                    ),
                                    _ => None,
                                }
                            }
                        }
                    }
                }
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            } if left == right => Some(true),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            } => {
                let left = left.as_ref().clone();
                let right = right.as_ref().clone();
                if self.bitvector_add_terms_proven_equal(&left, &right)
                    || self.count_fold_split_terms_proven_equal(&left, &right)
                    || self.range_fold_terms_alpha_equivalent(&left, &right)
                {
                    return Some(true);
                }

                if let Some((left, right)) =
                    bitvector_equality_after_additive_cancellation(&left, &right)
                {
                    return self.decide(&ConditionTerm::equal(left, right));
                }

                if let Some(equal) = self.exact_signed_intervals_equal(&left, &right) {
                    return Some(equal);
                }

                if self.has_condition_fact(ConditionTerm::equal(left.clone(), right.clone()), true)
                    || self
                        .has_condition_fact(ConditionTerm::equal(right.clone(), left.clone()), true)
                    || self.memory_loads_proven_equal(&left, &right)
                    || self.has_condition_fact(
                        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
                        true,
                    ) && self.has_condition_fact(
                        ConditionTerm::signed_greater_equal(left.clone(), right.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::pointer_offset_equal(
                            PointerOffsetTerm::scale_int32(left.clone(), 4),
                            PointerOffsetTerm::scale_int32(right.clone(), 4),
                        ),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::pointer_offset_equal(
                            PointerOffsetTerm::scale_int32(right.clone(), 4),
                            PointerOffsetTerm::scale_int32(left.clone(), 4),
                        ),
                        true,
                    )
                    || self.order_facts_force_equal(&left, &right)
                    || self.range_facts_force_equal(&left, &right)
                {
                    Some(true)
                } else if self
                    .has_condition_fact(ConditionTerm::equal(left.clone(), right.clone()), false)
                    || self.has_condition_fact(
                        ConditionTerm::equal(right.clone(), left.clone()),
                        false,
                    )
                    || bitvector_same_base_nonzero_const_offset(&left, &right)
                {
                    Some(false)
                } else if (self.has_condition_fact(
                    ConditionTerm::signed_less_equal(left.clone(), right.clone()),
                    true,
                ) && self.has_condition_fact(
                    ConditionTerm::signed_less_than(left.clone(), right.clone()),
                    false,
                )) || (self.has_condition_fact(
                    ConditionTerm::signed_greater_equal(left.clone(), right.clone()),
                    true,
                ) && self.has_condition_fact(
                    ConditionTerm::signed_greater_than(left.clone(), right.clone()),
                    false,
                )) {
                    Some(true)
                } else if self.decide(&ConditionTerm::signed_less_than(
                    left.clone(),
                    right.clone(),
                )) == Some(true)
                    || self.decide(&ConditionTerm::signed_greater_than(
                        left.clone(),
                        right.clone(),
                    )) == Some(true)
                    || self.has_condition_fact(
                        ConditionTerm::pointer_offset_equal(
                            PointerOffsetTerm::scale_int32(left.clone(), 4),
                            PointerOffsetTerm::scale_int32(right.clone(), 4),
                        ),
                        false,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::pointer_offset_equal(
                            PointerOffsetTerm::scale_int32(right.clone(), 4),
                            PointerOffsetTerm::scale_int32(left.clone(), 4),
                        ),
                        false,
                    )
                {
                    Some(false)
                } else {
                    None
                }
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt32,
                relation:
                    relation @ (crate::kernel::CompareRelation::LessThan
                    | crate::kernel::CompareRelation::LessEqual
                    | crate::kernel::CompareRelation::GreaterThan
                    | crate::kernel::CompareRelation::GreaterEqual),
                ..
            } if *relation != CompareRelation::Equal => self.decide_unsigned32_order(condition),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            } if left == right => Some(false),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left,
                right,
            } if left == right => Some(false),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            } if left == right => Some(true),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left,
                right,
            } if left == right => Some(true),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            } => {
                let left = left.as_ref().clone();
                let right = right.as_ref().clone();
                if let Some(result) = self.decide_signed_comparison_from_equal_constants(
                    &left,
                    &right,
                    |left, right| left < right,
                ) {
                    return Some(result);
                }
                if right == signed_int_min_term() || left == signed_int_max_term() {
                    return Some(false);
                }
                if self.subtract_same_const_order_fact(&left, &right, true)
                    || self.difference_graph_proves_order(&left, &right, true)
                    || (self.has_condition_fact(
                        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
                        true,
                    ) && self.has_condition_fact(
                        ConditionTerm::equal(left.clone(), right.clone()),
                        false,
                    ))
                    || self.has_condition_fact(
                        ConditionTerm::signed_greater_than(right.clone(), left.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_greater_equal(left.clone(), right.clone()),
                        false,
                    )
                    || self.has_upper_bound_below(&left, &right)
                    || self.has_successor_upper_bound_below(&left, &right)
                    || self.has_add_const_upper_bound_below(&left, &right)
                    || self.has_lower_bound_above(&right, &left)
                    || self.has_add_const_lower_bound_above(&right, &left)
                    || self.positive_offset_is_proven_above(&left, &right)
                    || self.positive_subtraction_is_proven_below(&left, &right)
                    // Consulted last: every earlier rule keeps its cost.
                    || self.has_subtract_const_upper_bound(&left, &right, true)
                    || self.has_subtract_const_lower_bound(&right, &left, true)
                {
                    Some(true)
                } else if self.has_condition_fact(
                    ConditionTerm::signed_greater_equal(left.clone(), right.clone()),
                    true,
                ) || self.has_condition_fact(
                    ConditionTerm::signed_less_equal(right.clone(), left.clone()),
                    true,
                ) || self.difference_graph_proves_order(&right, &left, true)
                    || self.order_facts_force_equal(&left, &right)
                {
                    Some(false)
                } else {
                    self.decide_signed_order_from_conditional_interval(&left, &right, true)
                }
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            } => {
                let left = left.as_ref().clone();
                let right = right.as_ref().clone();
                if let Some(result) = self.decide_signed_comparison_from_equal_constants(
                    &left,
                    &right,
                    |left, right| left <= right,
                ) {
                    return Some(result);
                }
                if order_holds_at_int32_extreme(&left, &right, false) {
                    return Some(true);
                }
                if self.difference_graph_proves_order(&left, &right, false)
                    || left.add_const_base(1).is_some_and(|base| {
                        self.has_condition_fact(
                            ConditionTerm::signed_less_than(base, right.clone()),
                            true,
                        )
                    })
                    || right.subtract_one_base().is_some_and(|base| {
                        let zero = Bitvector32Term::Constant(0);
                        left == zero
                            && (self.has_condition_fact(
                                ConditionTerm::signed_greater_than(base.clone(), zero.clone()),
                                true,
                            ) || self.has_lower_bound_above(&base, &zero))
                    })
                    || self.has_add_const_upper_bound_at_or_below(&left, &right)
                    || self.is_bounded_by_base_before_nonnegative_offset(&left, &right)
                    || self.has_condition_fact(
                        ConditionTerm::signed_less_than(left.clone(), right.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_greater_equal(right.clone(), left.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_greater_than(right.clone(), left.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_greater_than(left.clone(), right.clone()),
                        false,
                    )
                    || self.has_lower_bound_at_or_above(&right, &left)
                    || self.has_add_const_lower_bound_at_or_above(&right, &left)
                    || self.nonnegative_offset_is_proven_at_or_above(&left, &right)
                    || self.order_facts_force_equal(&left, &right)
                    // Consulted last: every earlier rule keeps its cost.
                    || self.has_subtract_const_upper_bound(&left, &right, false)
                    || self.has_subtract_const_lower_bound(&right, &left, false)
                {
                    Some(true)
                } else if self.has_condition_fact(
                    ConditionTerm::signed_greater_than(left.clone(), right.clone()),
                    true,
                ) {
                    Some(false)
                } else {
                    self.decide_signed_order_from_conditional_interval(&left, &right, false)
                }
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left,
                right,
            } => {
                let left = left.as_ref().clone();
                let right = right.as_ref().clone();
                if let Some(result) = self.decide_signed_comparison_from_equal_constants(
                    &left,
                    &right,
                    |left, right| left > right,
                ) {
                    return Some(result);
                }
                if right == signed_int_max_term() || left == signed_int_min_term() {
                    return Some(false);
                }
                if self.difference_graph_proves_order(&right, &left, true)
                    || self.has_condition_fact(
                        ConditionTerm::signed_less_than(right.clone(), left.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
                        false,
                    )
                    || self.has_lower_bound_above(&left, &right)
                    || self.has_add_const_lower_bound_above(&left, &right)
                    // The mirrors of the `<` rules for a successor and for
                    // the int32 maximum, so `x + 1 > x` and `INT32_MAX > x`
                    // are decided as `x < x + 1` and `x < INT32_MAX` are.
                    || self.positive_offset_is_proven_above(&right, &left)
                    || left == signed_int_max_term()
                        && self.decide(&ConditionTerm::signed_less_than(
                            right.clone(),
                            left.clone(),
                        )) == Some(true)
                {
                    Some(true)
                } else if self.has_condition_fact(
                    ConditionTerm::signed_less_equal(left.clone(), right.clone()),
                    true,
                ) || self.has_condition_fact(
                    ConditionTerm::signed_greater_equal(right.clone(), left.clone()),
                    true,
                ) || self.order_facts_force_equal(&left, &right)
                {
                    Some(false)
                } else {
                    self.decide_signed_order_from_conditional_interval(&right, &left, true)
                }
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left,
                right,
            } => {
                let left = left.as_ref().clone();
                let right = right.as_ref().clone();
                if let Some(result) = self.decide_signed_comparison_from_equal_constants(
                    &left,
                    &right,
                    |left, right| left >= right,
                ) {
                    return Some(result);
                }
                if order_holds_at_int32_extreme(&right, &left, false) {
                    return Some(true);
                }
                if self.difference_graph_proves_order(&right, &left, false)
                    || self.has_condition_fact(
                        ConditionTerm::signed_greater_than(left.clone(), right.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_less_equal(right.clone(), left.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_less_than(right.clone(), left.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_less_than(left.clone(), right.clone()),
                        false,
                    )
                    || self.has_lower_bound_at_or_above(&left, &right)
                    || self.has_add_const_lower_bound_at_or_above(&left, &right)
                    // The mirror of the `<=` successor rule, so `x + 1 >= x`
                    // is decided as `x <= x + 1` is.
                    || self.nonnegative_offset_is_proven_at_or_above(&right, &left)
                    || self.order_facts_force_equal(&left, &right)
                {
                    Some(true)
                } else if self.has_condition_fact(
                    ConditionTerm::signed_less_than(left.clone(), right.clone()),
                    true,
                ) {
                    Some(false)
                } else {
                    self.decide_signed_order_from_conditional_interval(&right, &left, false)
                }
            }
            _ => None,
        }
    }

    /// The order rules of a `uint32` order: equal operands, constants an
    /// equality pins, the extremes `0` and `UINT32_MAX`, the difference
    /// graph's unsigned domain, the fact itself in any of its spellings, and
    /// one recorded bound of either operand ([`Self::has_unsigned32_bound_between`]).
    /// Each is tried for the order and for its converse, which refutes it.
    fn decide_unsigned32_order(&self, condition: &ConditionTerm) -> Option<bool> {
        let (lower, upper, strict) = held_order_at(MachineIntegerType::UInt32, condition, true)?;
        if lower == upper {
            return Some(!strict);
        }
        if let (Some(lower), Some(upper)) = (
            self.signed_constant_known_equal(lower),
            self.signed_constant_known_equal(upper),
        ) {
            let (lower, upper) = (lower as u32, upper as u32);
            return Some(if strict {
                lower < upper
            } else {
                lower <= upper
            });
        }
        let holds = |lower: &Bitvector32Term, upper: &Bitvector32Term, strict: bool| {
            let (low, high) = (lower.as_const(), upper.as_const());
            if !strict && (low == Some(0) || high == Some(u32::MAX)) {
                return true;
            }
            if strict && (high == Some(0) || low == Some(u32::MAX)) {
                return false;
            }
            let order = OrderKind::Unsigned32.order(lower.clone(), upper.clone(), strict);
            self.difference_graph_proves(&order)
                || crate::kernel::proof::fact_reasoning::order_claim_forms(
                    &Proposition::ConditionIs(order, true),
                )
                .iter()
                .any(|form| {
                    matches!(form, Proposition::ConditionIs(condition, value)
                        if self.condition_facts.get(condition) == Some(value))
                })
                || (strict
                    && self.has_condition_fact(
                        ConditionTerm::unsigned_less_equal(lower.clone(), upper.clone()),
                        true,
                    )
                    && self.has_condition_fact(
                        ConditionTerm::equal(lower.clone(), upper.clone()),
                        false,
                    ))
                || self.has_unsigned32_bound_between(lower, upper, strict)
        };
        if holds(lower, upper, strict) {
            Some(true)
        } else if holds(upper, lower, !strict) {
            Some(false)
        } else {
            None
        }
    }

    /// Query equality already known to the trusted graph. This performs no
    /// arithmetic proof search, alias-component walk, or resource check.
    /// `false` means unknown, not unequal. Memory consumers must retain their
    /// structural-distinctness and separation checks around this query.
    pub(in crate::kernel) fn pointers_known_equal(&self, left: &Pointer, right: &Pointer) -> bool {
        self.equality_graph.are_equal(left, right)
    }

    /// True when some exact order fact strictly bounds `term` above
    /// (`term < y` for any `y`). A strict signed bound pins
    /// `term < INT_MAX`, which is what discharges `term + 1` overflow
    /// is checked from exact facts alone.
    pub(in crate::kernel) fn has_exact_strict_upper_bound(&self, term: &Bitvector32Term) -> bool {
        self.checked_order_bounds.strict_upper(term).is_some()
    }

    /// Whether the difference graph of these facts proves `left < right`
    /// (or `left <= right` when `require_strict` is false). This is the one
    /// order engine the condition decision and memory resolution read: it is
    /// maintained per fact and answers each query within `EDGE_LIMIT` edges,
    /// so it reads no collection that grows with the facts. A longer order
    /// chain is left undecided; a proof states an intermediate step.
    pub(in crate::kernel) fn difference_graph_proves_order(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        require_strict: bool,
    ) -> bool {
        self.difference_graph_proves(&order_condition(
            left.clone(),
            right.clone(),
            require_strict,
        ))
    }

    /// Whether the difference graph of these facts proves `condition`
    /// ([`Self::difference_graph_proves_order`]), at any format it orders.
    pub(in crate::kernel) fn difference_graph_proves(&self, condition: &ConditionTerm) -> bool {
        let graph = self.difference_graph.graph(|| {
            self.condition_facts
                .scan_for_upkeep()
                .map(|(condition, value)| (condition, *value))
                .collect()
        });
        graph.decide(condition) == Some(true)
    }

    #[cfg(test)]
    pub(in crate::kernel) fn reset_exact_order_evidence_visits() {
        EXACT_ORDER_EVIDENCE_VISITS.with(|visits| visits.set(0));
    }

    #[cfg(test)]
    pub(in crate::kernel) fn exact_order_evidence_visits() -> usize {
        EXACT_ORDER_EVIDENCE_VISITS.with(std::cell::Cell::get)
    }

    /// Retain the exact signed-order edges selected by a deterministic path
    /// decision. This deliberately accepts only syntactic edge joins (plus a
    /// context-free constant tail): equality, memory-DAG, quantified, and
    /// derived-edge joins need their own typed evidence before they may be
    /// exported as certificate provenance.
    pub(in crate::kernel) fn exact_signed_order_path_evidence(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        require_strict: bool,
    ) -> Option<Vec<SignedOrderDerivationStep>> {
        // Keep the exact source proposition alongside the normalized edge.
        // `condition_as_order_fact` intentionally normalizes polarity (for
        // example, false `x <= y` becomes `y < x`); check must check the
        // proposition that was actually present, not merely the normalized
        // form. This collection is local to derivation construction so
        // the durable evidence remains self-contained.
        let step = |condition: &ConditionTerm| {
            #[cfg(test)]
            EXACT_ORDER_EVIDENCE_VISITS.with(|visits| visits.set(visits.get() + 1));
            let value = *self.condition_facts.get(condition)?;
            condition_as_order_fact(condition, value).map(|(lower, upper, strict)| {
                SignedOrderDerivationStep {
                    lower,
                    upper,
                    strict,
                    premise: Proposition::ConditionIs(condition.clone(), value),
                }
            })
        };
        let bridging = crate::kernel::api::extended_dag_bridging_active();
        let terms_match = |current: &Bitvector32Term, other: &Bitvector32Term| {
            current == other
                || bridging
                    && crate::kernel::api::atomic_loads_equal_along_memory_derivations(
                        current, other, self,
                    )
        };
        // The edges a node can take: those written from it, those from a
        // constant at least as large when it is a constant, and, under
        // bridging, those from another snapshot's load of its cell
        // (`OrderFactsByLower`). They are visited in the reverse of the
        // facts' own order, as the walk over every order fact visited them,
        // so the walk finds the same path.
        let edges_from = |current: &Bitvector32Term| {
            let index = &self.order_facts_by_lower;
            let mut conditions = index.written_from(current).collect::<BTreeSet<_>>();
            if let Some(constant) = signed_bitvector_constant(current) {
                conditions.extend(index.constant_at_least(constant));
            }
            if bridging && let Bitvector32Term::MemoryLoad(_, pointer, kind) = current {
                conditions.extend(index.loads_of(pointer, *kind));
            }
            conditions
                .into_iter()
                .rev()
                .filter_map(step)
                .collect::<Vec<_>>()
        };
        let mut stack = vec![(left.clone(), false, Vec::new())];
        let mut seen = BTreeSet::new();
        while let Some((current, strict_so_far, path)) = stack.pop() {
            if !seen.insert((current.clone(), strict_so_far)) {
                continue;
            }
            let constant_connection = signed_bitvector_constant(&current)
                .zip(signed_bitvector_constant(right))
                .and_then(|(current, right)| (current <= right).then_some(current < right));
            if (terms_match(&current, right) || constant_connection.is_some())
                && (!require_strict || strict_so_far || constant_connection == Some(true))
                && !path.is_empty()
            {
                return Some(path);
            }
            for edge in edges_from(&current) {
                let constant_connection = signed_bitvector_constant(&current)
                    .zip(signed_bitvector_constant(&edge.lower))
                    .and_then(|(current, edge_left)| {
                        (current <= edge_left).then_some(current < edge_left)
                    });
                if !terms_match(&current, &edge.lower) && constant_connection.is_none() {
                    continue;
                }
                let mut extended = path.clone();
                extended.push(edge.clone());
                stack.push((
                    edge.upper.clone(),
                    strict_so_far || edge.strict || constant_connection == Some(true),
                    extended,
                ));
            }
        }
        None
    }

    /// The exact order facts at `format`, one of [`WIDE_ORDER_FORMATS`], that
    /// chain `left` up to `right`. Each step keeps the proposition the context holds, as
    /// [`Self::exact_signed_order_path_evidence`] does for `int32`. The chain
    /// meets `right` at the same canonical term; a constant connection is
    /// left to other rules, since `solve` writes no lemma for it.
    pub(in crate::kernel) fn exact_wide_order_path_evidence(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        require_strict: bool,
        format: MachineIntegerType,
    ) -> Option<Vec<SignedOrderDerivationStep>> {
        let canonical = crate::kernel::eval::canonical_term;
        // The facts of this kind filed under the node's canonical form, the
        // only edges the walk matches (`OrderFactsByLower`), visited in the
        // reverse of the facts' own order as before.
        let edges_from = |current: &Bitvector32Term| {
            self.order_facts_by_lower
                .wide_from(format, current)
                .collect::<BTreeSet<_>>()
                .into_iter()
                .rev()
                .filter_map(|condition| {
                    let value = *self.condition_facts.get(condition)?;
                    wide_order_fact(condition, value, format).map(|(lower, upper, strict)| {
                        SignedOrderDerivationStep {
                            lower,
                            upper,
                            strict,
                            premise: Proposition::ConditionIs(condition.clone(), value),
                        }
                    })
                })
                .collect::<Vec<_>>()
        };
        let target = canonical(right);
        let mut stack = vec![(canonical(left), false, Vec::new())];
        let mut seen = BTreeSet::new();
        while let Some((current, strict_so_far, path)) = stack.pop() {
            if !seen.insert((current.clone(), strict_so_far)) {
                continue;
            }
            if current == target && (!require_strict || strict_so_far) && !path.is_empty() {
                return Some(path);
            }
            for edge in edges_from(&current) {
                debug_assert_eq!(canonical(&edge.lower), current);
                let mut extended = path.clone();
                extended.push(edge.clone());
                stack.push((
                    canonical(&edge.upper),
                    strict_so_far || edge.strict,
                    extended,
                ));
            }
        }
        None
    }

    /// Whether written signed-order facts chain from `left` to `right`,
    /// strictly when `require_strict`.
    ///
    /// A non-constant node's edges are read from the endpoint index
    /// (`signed_order_bounds`), which files every written order fact under
    /// its lower endpoint, so a walk costs the edges it follows rather than
    /// every order fact at every node. The two matches no endpoint key
    /// spells read `OrderFactsByLower`: a constant node connects to any edge
    /// whose lower end is a constant at least as large, one range read, and
    /// with extended bridging a load connects to its forms at other
    /// snapshots, filed under its pointer and kind.
    pub(in crate::kernel) fn has_exact_order_path(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        require_strict: bool,
    ) -> bool {
        let bridging = crate::kernel::api::extended_dag_bridging_active();
        // Two forms of one load at different snapshots connect along
        // recorded memory-derivation edges; the walk is deterministic (exact
        // facts plus DAG edges, no ambient condition reasoning), so an exact
        // order path may link through it — inside the loadable prover's
        // extended-bridging scope only. Non-loads still match verbatim.
        let terms_match = |current: &Bitvector32Term, other: &Bitvector32Term| {
            current == other
                || bridging
                    && crate::kernel::api::atomic_loads_equal_along_memory_derivations(
                        current, other, self,
                    )
        };
        let mut stack = vec![(left.clone(), false)];
        let mut seen = BTreeSet::new();
        while let Some((current, strict_so_far)) = stack.pop() {
            if !seen.insert((current.clone(), strict_so_far)) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            let constant_connection = signed_bitvector_constant(&current)
                .zip(signed_bitvector_constant(right))
                .and_then(|(current, right)| (current <= right).then_some(current < right));
            if (terms_match(&current, right) || constant_connection.is_some())
                && (!require_strict || strict_so_far || constant_connection == Some(true))
            {
                return true;
            }
            // Bridging relates two loads only (`atomic_memory_load_equality_evidence`).
            let bridged_load = bridging && matches!(current, Bitvector32Term::MemoryLoad(..));
            if bridged_load || signed_bitvector_constant(&current).is_some() {
                // A constant node takes the edges from a constant at least
                // as large; a bridged load, those from a load of its cell at
                // any snapshot (`OrderFactsByLower`). No other edge matches
                // either node.
                let index = &self.order_facts_by_lower;
                let candidates = match (&current, signed_bitvector_constant(&current)) {
                    (_, Some(constant)) => index.constant_at_least(constant).collect::<Vec<_>>(),
                    (Bitvector32Term::MemoryLoad(_, pointer, kind), None) => {
                        index.loads_of(pointer, *kind).collect()
                    }
                    _ => Vec::new(),
                };
                for condition in candidates {
                    let Some((edge_left, edge_right, edge_strict)) = self
                        .condition_facts
                        .get(condition)
                        .and_then(|value| condition_as_order_fact(condition, *value))
                    else {
                        continue;
                    };
                    let constant_connection = signed_bitvector_constant(&current)
                        .zip(signed_bitvector_constant(&edge_left))
                        .and_then(|(current, edge_left)| {
                            (current <= edge_left).then_some(current < edge_left)
                        });
                    if terms_match(&current, &edge_left) || constant_connection.is_some() {
                        stack.push((
                            edge_right,
                            strict_so_far || edge_strict || constant_connection == Some(true),
                        ));
                    }
                }
                continue;
            }
            let Some(bounds) = self.signed_order_bounds.get(&current) else {
                continue;
            };
            for ((lower, upper, edge_strict, outgoing), _) in bounds.iter() {
                crate::instrumentation::record_deterministic_work(1);
                // Entries filed under a canonical alias carry the written
                // lower end, which an exact walk does not match.
                if *outgoing && *lower == current {
                    stack.push((upper.clone(), strict_so_far || *edge_strict));
                }
            }
        }
        false
    }

    pub(in crate::kernel) fn proves_order_condition_for_memory_resolution(
        &self,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        if crate::kernel::assumptions::reasoning_interrupted() {
            return false;
        }
        if value && self.decide_from_variable_chain(condition) == Some(true) {
            return true;
        }
        // A `uint32` bound below the sign bit is the signed pair
        // `0 <= term` and `term <= bound`, read the same way the
        // condition checker reads it (`unsigned_upper_bound_below_sign_bit`),
        // so the two provers agree on what a range's extent guard means.
        if value
            && let Some((term, bound, _)) = unsigned_upper_bound_below_sign_bit(condition, true)
        {
            return self.proves_order_condition_for_memory_resolution(
                &ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), term.clone()),
                true,
            ) && self.proves_order_condition_for_memory_resolution(
                &ConditionTerm::signed_less_equal(term.clone(), Bitvector32Term::Constant(bound)),
                true,
            );
        }
        condition_as_order_fact(condition, value).is_some_and(|(left, right, strict)| {
            // The extreme and successor rules are the ones the condition
            // checker reads the same way (`decide_from_order_facts`); the
            // successor rules run only after the path search has missed.
            if order_holds_at_int32_extreme(&left, &right, strict) {
                return true;
            }
            let simplified_left = self.simplify_bitvector_under_assumptions(&left);
            let simplified_right = self.simplify_bitvector_under_assumptions(&right);
            if self.difference_graph_proves_order(&simplified_left, &simplified_right, strict) {
                return true;
            }
            if let Some((below, above)) = successor_bound_as_strict_order(&left, &right, strict)
                && self.proves_order_condition_for_memory_resolution(
                    &ConditionTerm::signed_less_than(below, above),
                    true,
                )
            {
                return true;
            }
            constant_below_successor_as_order(&left, &right, strict).is_some_and(
                |((below, above, reduced_strict), base)| {
                    self.proves_order_condition_for_memory_resolution(
                        &order_condition(below, above, reduced_strict),
                        true,
                    ) && self.proves_order_condition_for_memory_resolution(
                        &ConditionTerm::signed_less_than(
                            base,
                            Bitvector32Term::Constant(i32::MAX as u32),
                        ),
                        true,
                    )
                },
            )
        })
    }
}

/// Splits both offsets into their addends and removes every addend they
/// share (one occurrence per match). Offsets are exact i64 sums of their
/// addends, so `C + L == C + R` holds exactly if and only if `L == R`.
pub(in crate::kernel) fn cancel_common_offset_addends(
    left: &crate::kernel::PointerOffsetTerm,
    right: &crate::kernel::PointerOffsetTerm,
) -> (
    crate::kernel::PointerOffsetTerm,
    crate::kernel::PointerOffsetTerm,
) {
    use crate::kernel::PointerOffsetTerm;
    fn addends(offset: &PointerOffsetTerm, out: &mut Vec<PointerOffsetTerm>) {
        match offset {
            PointerOffsetTerm::Add(left, right) => {
                addends(left, out);
                addends(right, out);
            }
            other => out.push(other.clone()),
        }
    }
    fn rebuild(addends: Vec<PointerOffsetTerm>) -> PointerOffsetTerm {
        addends
            .into_iter()
            .reduce(|sum, addend| PointerOffsetTerm::Add(Box::new(sum), Box::new(addend)))
            .unwrap_or(PointerOffsetTerm::Constant(0))
    }
    let mut left_addends = Vec::new();
    addends(left, &mut left_addends);
    let mut right_addends = Vec::new();
    addends(right, &mut right_addends);
    crate::instrumentation::record_deterministic_work(left_addends.len() + right_addends.len());
    // A multiset count: each addend is hashed once, and an addend shared
    // `k` times cancels `k` times, so the work is linear in the addends.
    let mut right_counts = std::collections::HashMap::<&PointerOffsetTerm, usize>::new();
    for addend in &right_addends {
        *right_counts.entry(addend).or_default() += 1;
    }
    let mut cancelled = std::collections::HashMap::<&PointerOffsetTerm, usize>::new();
    let mut left_rest = Vec::new();
    for addend in &left_addends {
        match right_counts.get_mut(addend) {
            Some(count) if *count > 0 => {
                *count -= 1;
                *cancelled.entry(addend).or_default() += 1;
            }
            _ => left_rest.push(addend.clone()),
        }
    }
    let mut right_rest = Vec::new();
    for addend in &right_addends {
        match cancelled.get_mut(addend) {
            Some(count) if *count > 0 => *count -= 1,
            _ => right_rest.push(addend.clone()),
        }
    }
    (rebuild(left_rest), rebuild(right_rest))
}

/// The largest alignment a fact may state; probes above it are pointless.
const MAX_PROBED_ALIGNMENT: u64 = 4096;

impl PureFactContext {
    /// Decides `aligned(pointer, alignment)` from the pointer's formation: a
    /// heap block base is allocator-aligned, and any other base needs a
    /// recorded alignment fact (from address-of or a contract). A constant
    /// byte displacement from such a base is then decided exactly. Anything
    /// else stays undecided; alignment is never inferred from a pointee type.
    pub(in crate::kernel) fn decide_pointer_alignment(
        &self,
        pointer: &Pointer,
        alignment: u64,
    ) -> Option<bool> {
        self.pointer_alignment_decision(pointer, alignment)
            .map(|(aligned, _)| aligned)
    }

    /// The decision together with the exact base fact it used, so a
    /// derivation can retain that premise for its check.
    pub(in crate::kernel) fn pointer_alignment_decision(
        &self,
        pointer: &Pointer,
        alignment: u64,
    ) -> Option<(bool, Option<Proposition>)> {
        self.pointer_formation_alignment_decision(pointer, alignment, true)
            .or_else(|| {
                // One checked concrete formation, not an alias-member search.
                // Equality is trusted kernel evidence; the formation rule still
                // proves the alignment and retains any explicit base premise.
                let storage = self.equality_graph.storage_address(pointer);
                (storage != *pointer)
                    .then(|| self.pointer_formation_alignment_decision(&storage, alignment, true))
                    .flatten()
            })
    }

    /// The existing single-premise alignment certificate encodes formation
    /// arithmetic, not address-class equality. Do not cite a class witness as
    /// though that restricted certificate also carried its equality support.
    pub(in crate::kernel) fn pointer_alignment_certificate_decision(
        &self,
        pointer: &Pointer,
        alignment: u64,
    ) -> Option<(bool, Option<Proposition>)> {
        self.pointer_formation_alignment_decision(pointer, alignment, false)
    }

    fn pointer_formation_alignment_decision(
        &self,
        pointer: &Pointer,
        alignment: u64,
        allow_class_witness: bool,
    ) -> Option<(bool, Option<Proposition>)> {
        if !alignment.is_power_of_two() {
            return None;
        }
        // The null pointer's address is zero, which every alignment divides.
        let null_fact = ConditionTerm::pointer_equal(pointer.clone(), Pointer::null());
        if self.decide(&null_fact) == Some(true) {
            return Some((true, Some(Proposition::ConditionIs(null_fact, true))));
        }
        let (base, displacement) = split_constant_displacement(&pointer.offset);
        let intrinsic_block_alignment = match &pointer.block {
            PointerBlock::Heap(_) => Some(crate::kernel::primitives::HEAP_ALLOCATION_ALIGNMENT),
            // A file-scope or static object's block is placed by the
            // compiler at its type's alignment, recorded when the block was
            // created.
            block => crate::kernel::primitives::registered_block_alignment(block),
        };
        let premise = if base.as_const() == Some(0)
            && intrinsic_block_alignment.is_some_and(|intrinsic| alignment <= intrinsic)
        {
            None
        } else {
            // A displacement that is a scaled index whose scale the alignment
            // divides (an element step of a struct pointer, say) cannot
            // change the residue, so the fact may be recorded on the pointer
            // without it.
            let reduced = drop_aligned_scaled_addends(&base, alignment);
            let candidates = std::iter::once(base.clone())
                .chain(reduced.filter(|reduced| *reduced != base))
                .collect::<Vec<_>>();
            let mut found = None;
            'candidates: for candidate in candidates {
                let base_pointer = Pointer {
                    block: pointer.block.clone(),
                    offset: candidate,
                };
                let mut probe = alignment;
                while probe <= MAX_PROBED_ALIGNMENT {
                    let premise_at = |pointer: &Pointer, alignment| {
                        self.equality_graph
                            .admitted
                            .pointer_alignment_facts
                            .get(&(pointer.clone(), alignment))
                            .and_then(|sources| sources.iter().next())
                            .cloned()
                            .or_else(|| {
                                let fact =
                                    ConditionTerm::pointer_aligned(pointer.clone(), alignment);
                                (self.exact_condition_value(&fact) == Some(true)).then_some(fact)
                            })
                    };
                    if let Some(fact) = premise_at(&base_pointer, probe) {
                        found = Some(Proposition::ConditionIs(fact, true));
                        break 'candidates;
                    }
                    let witness = allow_class_witness
                        .then(|| self.equality_graph.alignment_witness(&base_pointer))
                        .flatten()
                        .filter(|(known, _)| probe <= *known)
                        .and_then(|(known, source)| premise_at(&source, known));
                    if let Some(fact) = witness {
                        found = Some(Proposition::ConditionIs(fact, true));
                        break 'candidates;
                    }
                    probe *= 2;
                }
            }
            Some(found?)
        };
        Some((displacement.rem_euclid(alignment as i64) == 0, premise))
    }
}

impl PureFactContext {
    /// Equalities the address and tag structure decides beyond the plain
    /// address rules: two tagged addresses, a tagged address against zero,
    /// a masked tag against a value, and a masked term against zero.
    pub(in crate::kernel) fn decide_uint64_equality_extras(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> Option<bool> {
        let mut used = crate::kernel::eval::pointer_tags::UsedFacts::new();
        self.decide_uint64_equality_extras_citing(left, right, &mut used)
    }

    /// The complete pointer-word decision for a 64-bit equality, citing the
    /// exact facts used: the address rule, the alignment rule, and the tag
    /// extras, in that order.
    pub(in crate::kernel) fn decide_pointer_word_equality_citing(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        used: &mut crate::kernel::eval::pointer_tags::UsedFacts,
    ) -> Option<bool> {
        if let Some(pointer_condition) =
            ConditionTerm::address_equality_as_pointer_equality(left, right)
        {
            return self.decide_citing(&pointer_condition, used);
        }
        let condition = ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        };
        if let Some((pointer, alignment)) = condition.as_pointer_alignment() {
            let (aligned, premise) =
                self.pointer_alignment_certificate_decision(pointer, alignment)?;
            if let Some(premise) = premise {
                used.premises.push(premise);
            }
            return Some(aligned);
        }
        self.decide_uint64_equality_extras_citing(left, right, used)
    }

    fn decide_uint64_equality_extras_citing(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        used: &mut crate::kernel::eval::pointer_tags::UsedFacts,
    ) -> Option<bool> {
        use crate::kernel::eval::pointer_tags::{masked_tag_value, tag_bound, tagged_address_form};
        let left_form = tagged_address_form(left, self, used);
        let right_form = tagged_address_form(right, self, used);
        match (left_form, right_form) {
            (Some(left), Some(right)) => {
                if left.tag == right.tag {
                    return self.decide_citing(
                        &ConditionTerm::pointer_equal(left.pointer, right.pointer),
                        used,
                    );
                }
                if left.pointer == right.pointer {
                    return self
                        .decide_citing(&ConditionTerm::uint64_equal(left.tag, right.tag), used);
                }
                let (Some(left_tag), Some(right_tag)) =
                    (tag_bound(&left.tag), tag_bound(&right.tag))
                else {
                    return None;
                };
                let alignment = left_tag
                    .max(right_tag)
                    .checked_add(1)?
                    .checked_next_power_of_two()?;
                let tags_differ = self
                    .decide_citing(&ConditionTerm::uint64_equal(left.tag, right.tag), used)
                    == Some(false);
                let distinct = tags_differ
                    || self.decide_citing(
                        &ConditionTerm::pointer_equal(left.pointer.clone(), right.pointer.clone()),
                        used,
                    ) == Some(false);
                let both_aligned = self.decide_citing(
                    &ConditionTerm::pointer_aligned(left.pointer, alignment),
                    used,
                ) == Some(true)
                    && self.decide_citing(
                        &ConditionTerm::pointer_aligned(right.pointer, alignment),
                        used,
                    ) == Some(true);
                // Different low tags have different residues modulo alignment.
                // Otherwise, distinct aligned bases differ by at least that
                // alignment, so smaller tags cannot make the words coincide.
                (distinct && both_aligned).then_some(false)
            }
            (Some(form), None) | (None, Some(form)) => {
                let left_is_form =
                    tagged_address_form(left, self, &mut Default::default()).is_some();
                let other = if left_is_form { right } else { left };
                if other.uint64_as_const() != Some(0) {
                    return None;
                }
                let tag = tag_bound(&form.tag)?;
                let alignment = tag.checked_add(1)?.checked_next_power_of_two()?;
                let nonnull = self.decide_citing(
                    &ConditionTerm::pointer_equal(form.pointer.clone(), Pointer::null()),
                    used,
                ) == Some(false);
                let aligned = self.decide_citing(
                    &ConditionTerm::pointer_aligned(form.pointer, alignment),
                    used,
                ) == Some(true);
                // A non-null base aligned to `alignment` is at least
                // `alignment`, so adding a smaller tag cannot reach zero.
                (nonnull && aligned).then_some(false)
            }
            (None, None) => {
                if let Some(tag) = masked_tag_value(left, self, used) {
                    return self
                        .decide_citing(&ConditionTerm::uint64_equal(tag, right.clone()), used);
                }
                if let Some(tag) = masked_tag_value(right, self, used) {
                    return self
                        .decide_citing(&ConditionTerm::uint64_equal(left.clone(), tag), used);
                }
                self.decide_masked_zero(left, right, used)
            }
        }
    }

    /// `(x & m) == 0` holds when `x` is below the lowest set bit of `m`.
    fn decide_masked_zero(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        used: &mut crate::kernel::eval::pointer_tags::UsedFacts,
    ) -> Option<bool> {
        let masked = if right.uint64_as_const() == Some(0) {
            left
        } else if left.uint64_as_const() == Some(0) {
            right
        } else {
            return None;
        };
        let Bitvector32Term::Binary {
            format: MachineIntegerType::UInt64,
            op: MachineBinaryOp::BitwiseAnd,
            left: first,
            right: second,
        } = masked
        else {
            return None;
        };
        let (value, mask) = match (first.uint64_as_const(), second.uint64_as_const()) {
            (None, Some(mask)) => (first, mask),
            (Some(mask), None) => (second, mask),
            _ => return None,
        };
        if mask == 0 {
            return Some(true);
        }
        let bound = 1u64.checked_shl(mask.trailing_zeros())?;
        (self.decide_citing(
            &ConditionTerm::uint64_less_than(
                value.as_ref().clone(),
                Bitvector32Term::UInt64Constant(bound),
            ),
            used,
        ) == Some(true))
        .then_some(true)
    }
}

/// Separates the constant byte addends of an offset from its symbolic part,
/// rebuilding the symbolic part with the canonical constructor so it matches
/// the shape a recorded fact about the base pointer has.
/// The offset without its scaled-index addends whose byte scale `alignment`
/// divides; `None` when there is no such addend.
fn drop_aligned_scaled_addends(
    offset: &crate::kernel::PointerOffsetTerm,
    alignment: u64,
) -> Option<crate::kernel::PointerOffsetTerm> {
    use crate::kernel::PointerOffsetTerm;
    fn addends(offset: &PointerOffsetTerm, out: &mut Vec<PointerOffsetTerm>) {
        match offset {
            PointerOffsetTerm::Add(left, right) => {
                addends(left, out);
                addends(right, out);
            }
            other => out.push(other.clone()),
        }
    }
    let mut parts = Vec::new();
    addends(offset, &mut parts);
    let alignment = i64::try_from(alignment).ok()?;
    // A struct pointer steps by `(uint8 *)p + i * sizeof(struct)`, so the
    // scale may sit inside the index as a constant factor.
    fn constant_factor(term: &Bitvector32Term) -> Option<i64> {
        match term {
            binary_term!(Int32, Multiply, left, right) => left
                .as_const()
                .map(|constant| i64::from(constant as i32))
                .or_else(|| right.as_const().map(|constant| i64::from(constant as i32))),
            _ => None,
        }
    }
    let divisible = |part: &PointerOffsetTerm| match part {
        PointerOffsetTerm::Int32Scaled { value, byte_width }
        | PointerOffsetTerm::Int64Scaled {
            value, byte_width, ..
        } => {
            let scale = constant_factor(value)
                .and_then(|factor| factor.checked_mul(*byte_width))
                .unwrap_or(*byte_width);
            scale != 0 && scale % alignment == 0
        }
        _ => false,
    };
    if !parts.iter().any(&divisible) {
        return None;
    }
    Some(
        parts
            .into_iter()
            .filter(|part| !divisible(part))
            .reduce(PointerOffsetTerm::add)
            .unwrap_or(PointerOffsetTerm::Constant(0)),
    )
}

fn split_constant_displacement(
    offset: &crate::kernel::PointerOffsetTerm,
) -> (crate::kernel::PointerOffsetTerm, i64) {
    use crate::kernel::PointerOffsetTerm;
    fn addends(offset: &PointerOffsetTerm, out: &mut Vec<PointerOffsetTerm>) {
        match offset {
            PointerOffsetTerm::Add(left, right) => {
                addends(left, out);
                addends(right, out);
            }
            other => out.push(other.clone()),
        }
    }
    let mut parts = Vec::new();
    addends(offset, &mut parts);
    let mut displacement = 0i64;
    let mut symbolic = Vec::new();
    for part in parts {
        match part.as_const() {
            Some(constant) => displacement = displacement.wrapping_add(constant),
            None => symbolic.push(part),
        }
    }
    let base = symbolic
        .into_iter()
        .reduce(PointerOffsetTerm::add)
        .unwrap_or(PointerOffsetTerm::Constant(0));
    (base, displacement)
}

/// The operand, inclusive bound, and source strictness of a `uint32` upper
/// bound `x <=u c` (or `x <u c + 1`) held with `value`, in either
/// orientation or polarity, whose bound `c` lies below the sign bit.
///
/// Such a bound means exactly `0 <= x` and `x <= c` in signed arithmetic: a
/// word no larger than `c < 2^31` as unsigned has a clear sign bit, and for a
/// clear sign bit the two readings agree. That is the form order facts are
/// written in, so the condition checker decides it by deciding those two, and
/// a context that assumes it files those two beside it
/// (`PureFactContext::assume_condition`), so every reader of signed order
/// facts sees the range an unsigned test established. The recognizer is a
/// constant-size match on the condition's own shape.
pub(in crate::kernel) fn unsigned_upper_bound_below_sign_bit(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(&Bitvector32Term, u32, bool)> {
    let (left, right, strict) = held_order_at(MachineIntegerType::UInt32, condition, value)?;
    if left.as_const().is_some() {
        return None;
    }
    let bound = right.as_const()?;
    let bound = if strict { bound.checked_sub(1)? } else { bound };
    (bound <= i32::MAX as u32).then_some((left, bound, strict))
}

/// The operand, inclusive bound, and source strictness of a sixty-four-bit
/// unsigned upper bound `x <=u c` (or `x <u c + 1`) held with `value`, in
/// either orientation or polarity, whose bound `c` lies below `2^31`.
///
/// Such a bound pins `x` below the sign bit of its low word: `x` is exactly
/// its truncation `(uint32)x`, which as a signed word lies in `0..=c`. A
/// context that assumes the bound files that range on the truncation beside
/// it (`PureFactContext::assume_condition`), the sixty-four-bit counterpart
/// of [`unsigned_upper_bound_below_sign_bit`]. Constant-size match.
pub(in crate::kernel) fn uint64_upper_bound_below_sign_bit(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(&Bitvector32Term, u32, bool)> {
    let (left, right, strict) = match (condition, value) {
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessEqual,
                left: a,
                right: b,
            },
            true,
        )
        | (
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterThan,
                left: a,
                right: b,
            },
            false,
        ) => (a, b, false),
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessThan,
                left: a,
                right: b,
            },
            true,
        )
        | (
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterEqual,
                left: a,
                right: b,
            },
            false,
        ) => (a, b, true),
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterEqual,
                left: a,
                right: b,
            },
            true,
        )
        | (
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessThan,
                left: a,
                right: b,
            },
            false,
        ) => (b, a, false),
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterThan,
                left: a,
                right: b,
            },
            true,
        )
        | (
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessEqual,
                left: a,
                right: b,
            },
            false,
        ) => (b, a, true),
        _ => return None,
    };
    if left.uint64_as_const().is_some() {
        return None;
    }
    let bound = right.uint64_as_const()?;
    let bound = if strict { bound.checked_sub(1)? } else { bound };
    (bound <= i32::MAX as u64).then_some((left.as_ref(), bound as u32, strict))
}

impl PureFactContext {
    /// Decides `term <=u bound` for `bound < 2^31` as the signed pair
    /// `0 <= term` and `term <= bound`; see
    /// [`unsigned_upper_bound_below_sign_bit`]. True only when both are
    /// decided true, false as soon as either is decided false.
    fn decide_unsigned_upper_bound_by_signed_order(
        &self,
        term: &Bitvector32Term,
        bound: u32,
    ) -> Option<bool> {
        let nonnegative = self.decide(&ConditionTerm::signed_less_equal(
            Bitvector32Term::Constant(0),
            term.clone(),
        ));
        if nonnegative == Some(false) {
            return Some(false);
        }
        let below = self.decide(&ConditionTerm::signed_less_equal(
            term.clone(),
            Bitvector32Term::Constant(bound),
        ));
        match (nonnegative, below) {
            (_, Some(false)) => Some(false),
            (Some(true), Some(true)) => Some(true),
            _ => None,
        }
    }
}

/// A wrapped comparison of rebuilt terms can refute offset equality (equal
/// offsets have equal residues) but can affirm it only when both rebuilt
/// terms are exact; otherwise the equality stays undecided.
fn exact_or_unequal(decided: Option<bool>, exact: bool) -> Option<bool> {
    match decided {
        Some(true) if !exact => None,
        other => other,
    }
}

impl PureFactContext {
    /// [`Self::rebuilt_offset_is_exact`] on the four-byte element path. The
    /// path-fact recorder needs this for negative offset premises; memory
    /// resolution uses the width-specific form for positive index equality.
    pub(in crate::kernel) fn element_index_rebuild_is_exact(
        &self,
        offset: &crate::kernel::PointerOffsetTerm,
    ) -> bool {
        self.element_index_rebuild_is_exact_for_width(offset, 4)
    }

    /// Whether the offset's index at this element width is exact rather than
    /// merely its 32-bit residue.
    pub(in crate::kernel) fn element_index_rebuild_is_exact_for_width(
        &self,
        offset: &crate::kernel::PointerOffsetTerm,
        element_width: u32,
    ) -> bool {
        self.rebuilt_offset_is_exact(offset, element_width, false)
    }

    /// Whether the index or byte term the offset rebuilders produce for
    /// `offset` denotes the exact offset rather than a wrapped 32-bit value.
    /// `PointerOffsetTerm` semantics are exact i64, so equal rebuilt terms
    /// imply equal offsets only when every rebuilt addition (and, on the byte
    /// path, every scaling by a width) is proved not to overflow under the
    /// current facts. Constants and single index terms are always exact.
    fn rebuilt_offset_is_exact(
        &self,
        offset: &crate::kernel::PointerOffsetTerm,
        element_width: u32,
        byte_path: bool,
    ) -> bool {
        use crate::kernel::PointerOffsetTerm;
        let rebuild = |offset: &PointerOffsetTerm| {
            if byte_path {
                byte_offset_from_pointer_offset(offset)
            } else {
                crate::kernel::reasoning::element_index_from_offset(offset, element_width)
            }
        };
        match offset {
            PointerOffsetTerm::Constant(_) => true,
            // Full-width constants or checked unsigned bounds make the
            // element projection exact. The byte projection below still
            // requires a constant whose scaled byte displacement fits.
            PointerOffsetTerm::Int64Scaled {
                value,
                byte_width,
                unsigned,
            } => {
                if !byte_path && *byte_width != i64::from(element_width) {
                    return false;
                }
                if byte_path && *byte_width == 0 {
                    return true;
                }
                if !byte_path {
                    return crate::kernel::reasoning::element_index_from_offset_with_facts(
                        offset,
                        element_width,
                        self,
                    )
                    .is_some();
                }
                // An `Int64Scaled` scales its *sixty-four-bit* value, and the
                // byte rebuilder scales it with the thirty-two-bit
                // `Multiply`. So the thirty-two-bit overflow question is the
                // wrong question to ask about this term: it is answered from
                // the low word, and the term's own value is not that word. A
                // value whose low word is `0xFFFFFFFF` passes it — `-1 * 8`
                // does not overflow an `int32` — while the offset it really
                // names, for an unsigned index, is `8 * 4294967295`, and the
                // rebuilt `-8` then reads as the element *below* the base.
                //
                // What settles it is what `bbe71eba` found settles the
                // element side: a fact pinning the value to a number, with
                // the scaled product then required to occupy an `int32`,
                // which is all the rebuilt term can hold. Arithmetic alone
                // cannot, and saying so is the refusal. The fact has to be a
                // sixty-four-bit one: a thirty-two-bit fact names the low
                // word and leaves the rest, which is the shape that made
                // `0xFFFFFFFF` look like a clean `-1`.
                let Some(value) = crate::kernel::assumptions::exact_sixty_four_bit_constant(
                    value, *unsigned, self,
                ) else {
                    return false;
                };
                value
                    .checked_mul(*byte_width)
                    .is_some_and(|bytes| i32::try_from(bytes).is_ok())
            }
            PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                if !byte_path || *byte_width <= 1 {
                    return true;
                }
                let Ok(width) = u32::try_from(*byte_width) else {
                    return false;
                };
                self.decide(&ConditionTerm::signed_multiply_overflows(
                    value.as_ref().clone(),
                    Bitvector32Term::Constant(width),
                )) == Some(false)
            }
            PointerOffsetTerm::Add(left, right)
                if left.as_ref() == &PointerOffsetTerm::Constant(0) =>
            {
                self.rebuilt_offset_is_exact(right, element_width, byte_path)
            }
            PointerOffsetTerm::Add(left, right)
                if right.as_ref() == &PointerOffsetTerm::Constant(0) =>
            {
                self.rebuilt_offset_is_exact(left, element_width, byte_path)
            }
            PointerOffsetTerm::Add(left, right) => {
                if !(self.rebuilt_offset_is_exact(left, element_width, byte_path)
                    && self.rebuilt_offset_is_exact(right, element_width, byte_path))
                {
                    return false;
                }
                match (rebuild(left), rebuild(right)) {
                    (Some(left), Some(right)) => {
                        self.decide(&ConditionTerm::signed_add_overflows(left, right))
                            == Some(false)
                    }
                    _ => false,
                }
            }
            PointerOffsetTerm::Variable(_) => false,
        }
    }
}

#[cfg(test)]
thread_local! {
    static EXACT_ORDER_EVIDENCE_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// An order fact at `format`, held with `value`, as the references
/// `(lower, upper, strict)` for `lower < upper` (strict) or `lower <=
/// upper`: `>` and `>=` swap their operands, and a false order is the
/// reversed order with the opposite strictness. Constant-size match.
pub(in crate::kernel) fn held_order_at(
    format: MachineIntegerType,
    condition: &ConditionTerm,
    value: bool,
) -> Option<(&Bitvector32Term, &Bitvector32Term, bool)> {
    let ConditionTerm::Compare {
        format: condition_format,
        relation,
        left,
        right,
    } = condition
    else {
        return None;
    };
    if *condition_format != format {
        return None;
    }
    let (lower_first, strict) = match relation {
        CompareRelation::LessThan => (true, true),
        CompareRelation::LessEqual => (true, false),
        CompareRelation::GreaterThan => (false, true),
        CompareRelation::GreaterEqual => (false, false),
        CompareRelation::Equal => return None,
    };
    let (lower, upper) = if lower_first {
        (left.as_ref(), right.as_ref())
    } else {
        (right.as_ref(), left.as_ref())
    };
    Some(if value {
        (lower, upper, strict)
    } else {
        (upper, lower, !strict)
    })
}

pub(in crate::kernel) fn condition_as_uint64_order_fact(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(Bitvector32Term, Bitvector32Term, bool)> {
    held_order_at(MachineIntegerType::UInt64, condition, value)
        .map(|(lower, upper, strict)| (lower.clone(), upper.clone(), strict))
}

/// The `uint32` counterpart of [`condition_as_uint64_order_fact`].
pub(in crate::kernel) fn condition_as_uint32_order_fact(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(Bitvector32Term, Bitvector32Term, bool)> {
    held_order_at(MachineIntegerType::UInt32, condition, value)
        .map(|(lower, upper, strict)| (lower.clone(), upper.clone(), strict))
}

/// The formats whose order facts the format-indexed order walk
/// ([`PureFactContext::exact_wide_order_path_evidence`]) follows: the 64-bit
/// orders and the `uint32` order. The `int32` order has its own walk
/// ([`PureFactContext::exact_signed_order_path_evidence`]).
pub(in crate::kernel) const WIDE_ORDER_FORMATS: [MachineIntegerType; 3] = [
    MachineIntegerType::UInt64,
    MachineIntegerType::Int64,
    MachineIntegerType::UInt32,
];

/// An order fact at `format`, one of [`WIDE_ORDER_FORMATS`], as `(lower,
/// upper, strict)`.
pub(in crate::kernel) fn wide_order_fact(
    condition: &ConditionTerm,
    value: bool,
    format: MachineIntegerType,
) -> Option<(Bitvector32Term, Bitvector32Term, bool)> {
    held_order_at(format, condition, value)
        .map(|(lower, upper, strict)| (lower.clone(), upper.clone(), strict))
}

impl PureFactContext {
    /// Check the full unsigned value's range through its own bound index.
    /// This proves that taking its low word preserves its nonnegative signed
    /// value; a bound on the low word alone supplies no evidence here.
    pub(in crate::kernel) fn uint64_index_fits_int32(&self, term: &Bitvector32Term) -> bool {
        let guard = ConditionTerm::uint64_less_equal(
            term.clone(),
            Bitvector32Term::UInt64Constant(i32::MAX as u64),
        );
        if guard.reflexive_value() == Some(true)
            || self.exact_condition_value(&guard) == Some(true)
            || self.decide_uint64_constant_order_bounds_inner(&guard, true) == Some(true)
        {
            return true;
        }
        // `x - c` for a constant `c` fits where `x` does and the
        // difference does not wrap, `c <= x`. Both are 64-bit facts about
        // `x` itself.
        if let Bitvector32Term::Binary {
            format: MachineIntegerType::UInt64,
            op: MachineBinaryOp::Subtract,
            left: minuend,
            right: subtrahend,
        } = term
            && subtrahend.uint64_as_const().is_some()
        {
            return self.uint64_index_fits_int32(minuend)
                && self.decide(&ConditionTerm::uint64_less_equal(
                    subtrahend.as_ref().clone(),
                    minuend.as_ref().clone(),
                )) == Some(true);
        }
        false
    }

    /// The signed counterpart: the full signed value lies in `0..=INT_MAX`,
    /// by 64-bit signed order facts on the value itself, so its low word is
    /// the value.
    pub(in crate::kernel) fn int64_index_fits_int32(&self, term: &Bitvector32Term) -> bool {
        self.decide(&ConditionTerm::int64_signed_less_equal(
            Bitvector32Term::Int64Constant(0),
            term.clone(),
        )) == Some(true)
            && self.decide(&ConditionTerm::int64_signed_less_equal(
                term.clone(),
                Bitvector32Term::Int64Constant(i32::MAX as i64),
            )) == Some(true)
    }

    /// An unsigned 64-bit comparison of signed values read as unsigned,
    /// `(uint64)i < (uint64)n`, or of one beside a constant at most
    /// `i64::MAX`: the bound a `long` range bound or index is given
    /// ([`crate::kernel::wide_range_bounds`]). When each signed value is
    /// decided nonnegative the two orders agree, so the signed comparison
    /// answers. Anything else is left to the other rules.
    pub(super) fn decide_unsigned_order_of_nonnegative_signed(
        &self,
        condition: &ConditionTerm,
    ) -> Option<bool> {
        type Signed = fn(Bitvector32Term, Bitvector32Term) -> ConditionTerm;
        let (left, right, signed): (_, _, Signed) = match condition {
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessThan,
                left: a,
                right: b,
            } => (a, b, ConditionTerm::int64_signed_less_than),
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessEqual,
                left: a,
                right: b,
            } => (a, b, ConditionTerm::int64_signed_less_equal),
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterThan,
                left: a,
                right: b,
            } => (a, b, ConditionTerm::int64_signed_greater_than),
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterEqual,
                left: a,
                right: b,
            } => (a, b, ConditionTerm::int64_signed_greater_equal),
            _ => return None,
        };
        let reinterpreted = |term: &Bitvector32Term| match term {
            Bitvector32Term::UInt64FromInt64(value) => Some(value.as_ref().clone()),
            _ => None,
        };
        if reinterpreted(left).is_none() && reinterpreted(right).is_none() {
            return None;
        }
        let as_signed = |term: &Bitvector32Term| {
            if let Some(value) = reinterpreted(term) {
                let nonnegative = self.decide(&ConditionTerm::int64_signed_less_equal(
                    Bitvector32Term::Int64Constant(0),
                    value.clone(),
                )) == Some(true);
                return nonnegative.then_some(value);
            }
            let constant = i64::try_from(term.uint64_as_const()?).ok()?;
            Some(Bitvector32Term::Int64Constant(constant))
        };
        let left = as_signed(left)?;
        let right = as_signed(right)?;
        self.decide(&signed(left, right))
    }

    /// Strengthen a constant bound using only the queried nonconstant endpoint's
    /// index. Never walk a shared constant's incident edges or unrelated facts.
    pub(super) fn decide_uint64_constant_order_bounds(
        &self,
        condition: &ConditionTerm,
    ) -> Option<bool> {
        self.decide_uint64_constant_order_bounds_inner(condition, false)
    }

    fn decide_uint64_constant_order_bounds_inner(
        &self,
        condition: &ConditionTerm,
        literal_only: bool,
    ) -> Option<bool> {
        let (left, right, mut operator) = match condition {
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessThan,
                left: a,
                right: b,
            } => (a, b, 0),
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessEqual,
                left: a,
                right: b,
            } => (a, b, 1),
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterThan,
                left: a,
                right: b,
            } => (a, b, 2),
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterEqual,
                left: a,
                right: b,
            } => (a, b, 3),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: a,
                right: b,
            } => (a, b, 4),
            _ => return None,
        };
        let (term, limit) = if let Some(limit) = right.uint64_as_const() {
            (left.as_ref(), limit)
        } else {
            let limit = left.uint64_as_const()?;
            operator = match operator {
                0 => 2,
                1 => 3,
                2 => 0,
                3 => 1,
                _ => 4,
            };
            (right.as_ref(), limit)
        };
        let bounds = self.uint64_order_bounds.get(term)?;
        for (endpoint, other, strict, upper) in bounds.keys() {
            crate::instrumentation::record_deterministic_work(1);
            let bound = if literal_only {
                other.uint64_as_const()
            } else {
                self.wide_constant_from_equalities(other)
            };
            let Some(bound) = bound else {
                continue;
            };
            let bound = if *strict {
                if *upper {
                    bound.checked_sub(1)
                } else {
                    bound.checked_add(1)
                }
            } else {
                Some(bound)
            };
            let Some(bound) = bound else {
                continue;
            };
            let answer = match (operator, *upper) {
                (0, true) if bound < limit => Some(true),
                (1, true) if bound <= limit => Some(true),
                (2, true) if bound <= limit => Some(false),
                (3, true) if bound < limit => Some(false),
                (0, false) if bound >= limit => Some(false),
                (1, false) if bound > limit => Some(false),
                (2, false) if bound > limit => Some(true),
                (3, false) if bound >= limit => Some(true),
                (4, true) if bound < limit => Some(false),
                (4, false) if bound > limit => Some(false),
                _ => None,
            };
            let Some(answer) = answer else {
                continue;
            };
            let (a, b) = if *upper {
                (endpoint.clone(), other.clone())
            } else {
                (other.clone(), endpoint.clone())
            };
            // The index normalizes negated/reversed comparisons. Recover an
            // actual source fact through four exact lookups so expansion cites
            // the premise that was held, including its original truth value.
            let candidates = if *strict {
                [
                    (ConditionTerm::uint64_less_than(a.clone(), b.clone()), true),
                    (
                        ConditionTerm::uint64_greater_than(b.clone(), a.clone()),
                        true,
                    ),
                    (
                        ConditionTerm::uint64_greater_equal(a.clone(), b.clone()),
                        false,
                    ),
                    (ConditionTerm::uint64_less_equal(b, a), false),
                ]
            } else {
                [
                    (ConditionTerm::uint64_less_equal(a.clone(), b.clone()), true),
                    (
                        ConditionTerm::uint64_greater_equal(b.clone(), a.clone()),
                        true,
                    ),
                    (
                        ConditionTerm::uint64_greater_than(a.clone(), b.clone()),
                        false,
                    ),
                    (ConditionTerm::uint64_less_than(b, a), false),
                ]
            };
            if candidates
                .iter()
                .any(|(fact, value)| self.exact_condition_value(fact) == Some(*value))
            {
                return Some(answer);
            }
        }
        None
    }

    /// Follow only upper edges in the operand's indexed uint64 order graph.
    /// Each node is visited once; unrelated facts are never read.
    fn uint64_small_upper_bound(&self, term: &Bitvector32Term) -> Option<u64> {
        let mut stack = vec![crate::kernel::eval::canonical_term(term)];
        let mut seen = BTreeSet::new();
        let mut best = None;
        while let Some(term) = stack.pop() {
            if !seen.insert(term.clone()) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            if let Some(value) = self.wide_constant_from_equalities(&term) {
                best = Some(best.map_or(value, |old: u64| old.min(value)));
                continue;
            }
            if let Some(edges) = self.uint64_order_bounds.get(&term) {
                for (_, upper, strict, forward) in edges.keys() {
                    crate::instrumentation::record_deterministic_work(1);
                    if !forward {
                        continue;
                    }
                    if let Some(value) = self.wide_constant_from_equalities(upper) {
                        if let Some(value) = if *strict {
                            value.checked_sub(1)
                        } else {
                            Some(value)
                        } {
                            best = Some(best.map_or(value, |old: u64| old.min(value)));
                        }
                    } else {
                        stack.push(crate::kernel::eval::canonical_term(upper));
                    }
                }
            }
        }
        best
    }

    /// Whether held 64-bit order facts chain from `lower` up to `upper`,
    /// and whether some chain does so strictly: `Some(true)` for a strict
    /// chain, `Some(false)` for a chain of `<=` only, `None` for no chain.
    ///
    /// One walk over the queried kind's direction-split edges, from `lower`
    /// along upper edges, or from `upper` along lower edges when `lower` is
    /// a literal. Each term is visited at most twice, once reached strictly
    /// and once not, and only the edges leaving a visited term in the
    /// walk's direction are read. A
    /// literal is an end of a chain and never a step in one: its edges name
    /// every term bounded by it, related to the question or not. Terms join
    /// by their canonical spelling; a visited term and the far end that
    /// both have a constant value join by comparing the values, as the kind
    /// compares them.
    fn wide_order_chain(
        &self,
        lower: &Bitvector32Term,
        upper: &Bitvector32Term,
        unsigned: bool,
    ) -> Option<bool> {
        let literal = |term: &Bitvector32Term| {
            term.uint64_as_const().is_some() || term.int64_as_const().is_some()
        };
        let lower = crate::kernel::eval::canonical_term(lower);
        let upper = crate::kernel::eval::canonical_term(upper);
        let upward = !literal(&lower);
        let (start, goal) = if upward {
            (lower, upper)
        } else {
            (upper, lower)
        };
        // Only the edges leaving a term in the walk's direction are read.
        let index = &self.wide_order_edges[usize::from(!unsigned)][usize::from(!upward)];
        let goal_constant = self.wide_constant_from_equalities(&goal);
        // How a visited value and the goal's value order along the walk.
        let toward_goal = |value: u64, goal: u64| {
            let (below, above) = if upward { (value, goal) } else { (goal, value) };
            if unsigned {
                below.cmp(&above)
            } else {
                (below as i64).cmp(&(above as i64))
            }
        };
        let mut stack = vec![(start, false)];
        let mut seen = BTreeSet::new();
        let mut chained = None;
        while let Some((term, strict_so_far)) = stack.pop() {
            if !seen.insert((term.clone(), strict_so_far)) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            let joined = if term == goal {
                Some(strict_so_far)
            } else {
                self.wide_constant_from_equalities(&term)
                    .zip(goal_constant)
                    .and_then(|(value, goal)| match toward_goal(value, goal) {
                        std::cmp::Ordering::Less => Some(true),
                        std::cmp::Ordering::Equal => Some(strict_so_far),
                        std::cmp::Ordering::Greater => None,
                    })
            };
            match joined {
                Some(true) => return Some(true),
                Some(false) => chained = Some(false),
                None => {}
            }
            if literal(&term) {
                continue;
            }
            let Some(edges) = index.get(&term) else {
                continue;
            };
            for (other, strict) in edges.keys() {
                crate::instrumentation::record_deterministic_work(1);
                stack.push((other.clone(), strict_so_far || *strict));
            }
        }
        chained
    }

    /// Decide a 64-bit order comparison from a chain of held order facts of
    /// its own kind, signed or unsigned: transitivity, a constant bound
    /// reached through a chain, and `a <= b` with `a != b`. The reversed
    /// chain refutes: `b <= a` refutes `a < b`, and `b < a` refutes `a <= b`.
    pub(super) fn decide_wide_order_chain(&self, condition: &ConditionTerm) -> Option<bool> {
        let (lower, upper, strict, unsigned) = match condition_as_uint64_order_fact(condition, true)
        {
            Some((lower, upper, strict)) => (lower, upper, strict, true),
            None => {
                let (lower, upper, strict) = condition_as_int64_order_fact(condition, true)?;
                (lower, upper, strict, false)
            }
        };
        // An unsigned value held unequal to zero is at least one.
        if unsigned
            && matches!(
                (lower.uint64_as_const(), strict),
                (Some(0), true) | (Some(1), false)
            )
            && [
                ConditionTerm::uint64_equal(upper.clone(), Bitvector32Term::UInt64Constant(0)),
                ConditionTerm::uint64_equal(Bitvector32Term::UInt64Constant(0), upper.clone()),
            ]
            .iter()
            .any(|zero| self.exact_condition_value(zero) == Some(false))
        {
            return Some(true);
        }
        match self.wide_order_chain(&lower, &upper, unsigned) {
            Some(true) => return Some(true),
            Some(false) if !strict => return Some(true),
            Some(false) => {
                let equal = ConditionTerm::int64_equal(lower.clone(), upper.clone());
                if self.exact_condition_value(&equal) == Some(false)
                    || self.exact_condition_value(&ConditionTerm::int64_equal(
                        upper.clone(),
                        lower.clone(),
                    )) == Some(false)
                {
                    return Some(true);
                }
            }
            None => {}
        }
        match self.wide_order_chain(&upper, &lower, unsigned) {
            Some(true) => Some(false),
            Some(false) if strict => Some(false),
            _ => None,
        }
    }

    /// Within the signed word's nonnegative range, truncation preserves
    /// uint64 order exactly. The range checks are required on both operands.
    pub(super) fn decide_small_uint64_index_order(
        &self,
        condition: &ConditionTerm,
    ) -> Option<bool> {
        if let Some((left, right, strict)) = condition_as_uint64_order_fact(condition, true) {
            let left = crate::kernel::eval::canonical_term(&left);
            let right = crate::kernel::eval::canonical_term(&right);
            if let Some(bounds) = self.uint64_order_bounds.get(&left) {
                for (_, other, held_strict, forward) in bounds.keys() {
                    crate::instrumentation::record_deterministic_work(1);
                    if crate::kernel::eval::canonical_term(other) != right {
                        continue;
                    }
                    if *forward && (!strict || *held_strict) {
                        return Some(true);
                    }
                    if !*forward && (strict || *held_strict) {
                        return Some(false);
                    }
                }
            }
        }
        if let Some(guard) = condition
            .uint64_successor_guard()
            .or_else(|| condition.uint64_subtraction_guard())
            .or_else(|| condition.uint64_remainder_bound_guard())
            && self.decide(&guard) == Some(true)
        {
            return Some(true);
        }
        if let Some(guards) = condition
            .uint64_subtraction_upper_bound_guards()
            .or_else(|| condition.uint64_partial_restoration_upper_bound_guards())
            && guards.iter().all(|guard| self.decide(guard) == Some(true))
        {
            return Some(true);
        }
        if let ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::LessEqual,
            left,
            right,
        } = condition
        {
            let limit = right.uint64_as_const()?;
            if self.uint64_small_upper_bound(left)? <= limit {
                return Some(true);
            }
            return None;
        }
        if let Some(guards) = condition.nonnegative_division_bound_guards()
            && guards.iter().all(|guard| self.decide(guard) == Some(true))
        {
            return Some(true);
        }
        let (left, right, strict) = condition_as_order_fact(condition, true)?;
        let small = |term: &Bitvector32Term| match term {
            Bitvector32Term::Constant(value) | Bitvector32Term::UInt32Constant(value)
                if *value <= i32::MAX as u32 =>
            {
                Some(*value as u64)
            }
            _ => None,
        };
        // Truncation commutes with addition modulo 2^32, so a truncated
        // term plus a constant is the truncation of the 64-bit sum, signed
        // or unsigned. The range check below is made on that sum.
        let truncated = |term: &Bitvector32Term, unsigned: bool| match term {
            Bitvector32Term::UInt32From64(value) => Some(value.as_ref().clone()),
            binary_term!(Int32, Add, left, right) => {
                let (value, constant) = match (left.as_ref(), right.as_ref()) {
                    (Bitvector32Term::UInt32From64(value), constant)
                    | (constant, Bitvector32Term::UInt32From64(value)) => (value, small(constant)?),
                    _ => return None,
                };
                Some(if unsigned {
                    Bitvector32Term::uint64_add(
                        value.as_ref().clone(),
                        Bitvector32Term::UInt64Constant(constant),
                    )
                } else {
                    Bitvector32Term::int64_add(
                        value.as_ref().clone(),
                        Bitvector32Term::Int64Constant(constant as i64),
                    )
                })
            }
            _ => None,
        };
        if truncated(&left, true).is_none() && truncated(&right, true).is_none() {
            return None;
        }
        let wide = |term: &Bitvector32Term, unsigned: bool| {
            truncated(term, unsigned).or_else(|| {
                small(term).map(|value| {
                    if unsigned {
                        Bitvector32Term::UInt64Constant(value)
                    } else {
                        Bitvector32Term::Int64Constant(value as i64)
                    }
                })
            })
        };
        // Read as unsigned values: both at most `INT_MAX`.
        let a = wide(&left, true)?;
        let b = wide(&right, true)?;
        let unsigned_small = |term: &Bitvector32Term| {
            self.uint64_small_upper_bound(term)
                .is_some_and(|bound| bound <= i32::MAX as u64)
        };
        if unsigned_small(&a) && unsigned_small(&b) {
            if a.uint64_as_const() == Some(0) && !strict {
                return Some(true);
            }
            let comparison = if strict {
                ConditionTerm::uint64_less_than(a, b)
            } else {
                ConditionTerm::uint64_less_equal(a, b)
            };
            return self.decide(&comparison);
        }
        // Read as signed values: both in `0..=INT_MAX`, where the low word
        // is the value and the two readings of the order agree.
        let a = wide(&left, false)?;
        let b = wide(&right, false)?;
        let signed_small = |term: &Bitvector32Term| {
            self.wide_order_chain(&Bitvector32Term::Int64Constant(0), term, false)
                .is_some()
                && self
                    .wide_order_chain(
                        term,
                        &Bitvector32Term::Int64Constant(i32::MAX as i64),
                        false,
                    )
                    .is_some()
        };
        if !signed_small(&a) || !signed_small(&b) {
            return None;
        }
        let comparison = if strict {
            ConditionTerm::int64_signed_less_than(a, b)
        } else {
            ConditionTerm::int64_signed_less_equal(a, b)
        };
        self.decide(&comparison)
    }
}

#[cfg(test)]
mod slice_index_tests {
    use super::*;

    #[test]
    fn wide_order_chains_decide_by_kind_and_refute_by_the_reversed_chain() {
        let v = |n: u64| Bitvector32Term::Variable(Variable(997000 + n));
        let (a, b, c, d) = (v(0), v(1), v(2), v(3));
        type Order = fn(Bitvector32Term, Bitvector32Term) -> ConditionTerm;
        let kinds: [(Order, Order); 2] = [
            (
                ConditionTerm::uint64_less_than,
                ConditionTerm::uint64_less_equal,
            ),
            (
                ConditionTerm::int64_signed_less_than,
                ConditionTerm::int64_signed_less_equal,
            ),
        ];
        for (index, (lt, le)) in kinds.iter().enumerate() {
            let facts = PureFactContext::new()
                .assume_condition(lt(a.clone(), b.clone()), true)
                .assume_condition(le(b.clone(), c.clone()), true)
                .assume_condition(le(c.clone(), d.clone()), true);
            assert_eq!(facts.decide(&lt(a.clone(), d.clone())), Some(true));
            assert_eq!(facts.decide(&le(a.clone(), d.clone())), Some(true));
            assert_eq!(facts.decide(&le(b.clone(), d.clone())), Some(true));
            // `b <= c <= d` has no strict step.
            assert_eq!(facts.decide(&lt(b.clone(), d.clone())), None);
            // The reversed chain refutes.
            assert_eq!(facts.decide(&lt(d.clone(), a.clone())), Some(false));
            assert_eq!(facts.decide(&le(d.clone(), a.clone())), Some(false));
            assert_eq!(facts.decide(&lt(d.clone(), b.clone())), Some(false));
            assert_eq!(facts.decide(&le(d.clone(), b.clone())), None);
            // A chain of one kind says nothing about the other.
            let (other_lt, other_le) = kinds[1 - index];
            assert_eq!(facts.decide(&other_lt(a.clone(), d.clone())), None);
            assert_eq!(facts.decide(&other_le(a.clone(), d.clone())), None);
            // `<=` with a held disequality is strict.
            let distinct = PureFactContext::new()
                .assume_condition(le(a.clone(), b.clone()), true)
                .assume_condition(ConditionTerm::int64_equal(a.clone(), b.clone()), false);
            assert_eq!(distinct.decide(&lt(a.clone(), b.clone())), Some(true));
            let unrelated = PureFactContext::new()
                .assume_condition(lt(a.clone(), b.clone()), true)
                .assume_condition(lt(c.clone(), d.clone()), true);
            assert_eq!(unrelated.decide(&lt(a.clone(), d.clone())), None);
        }
    }

    #[test]
    fn wide_order_chains_reach_constants_as_their_kind_compares_them() {
        let a = Bitvector32Term::Variable(Variable(997100));
        let b = Bitvector32Term::Variable(Variable(997101));
        let u = Bitvector32Term::UInt64Constant;
        let unsigned = PureFactContext::new()
            .assume_condition(ConditionTerm::uint64_less_than(a.clone(), b.clone()), true)
            .assume_condition(ConditionTerm::uint64_less_equal(b.clone(), u(10)), true)
            .assume_condition(ConditionTerm::uint64_less_equal(u(5), a.clone()), true);
        let lt = ConditionTerm::uint64_less_than;
        let le = ConditionTerm::uint64_less_equal;
        assert_eq!(unsigned.decide(&lt(a.clone(), u(10))), Some(true));
        // `a < b <= 10` entails `a <= 9`, which the difference graph reads.
        assert_eq!(unsigned.decide(&le(a.clone(), u(9))), Some(true));
        assert_eq!(unsigned.decide(&lt(a.clone(), u(u64::MAX))), Some(true));
        assert_eq!(unsigned.decide(&lt(u(5), b.clone())), Some(true));
        assert_eq!(unsigned.decide(&lt(u(4), a.clone())), Some(true));
        assert_eq!(unsigned.decide(&lt(u(5), a.clone())), None);
        assert_eq!(unsigned.decide(&lt(b.clone(), u(5))), Some(false));
        // An unsigned bound above the signed range is not a signed bound:
        // `a <=u 2^63` allows `a` to be negative as an int64.
        let high = 1u64 << 63;
        let wide = PureFactContext::new()
            .assume_condition(le(a.clone(), b.clone()), true)
            .assume_condition(le(b.clone(), u(high)), true);
        assert_eq!(wide.decide(&le(a.clone(), u(high))), Some(true));
        assert_eq!(
            wide.decide(&ConditionTerm::int64_signed_less_equal(a.clone(), u(high))),
            None
        );
        assert_eq!(
            wide.decide(&ConditionTerm::int64_signed_less_equal(u(0), a.clone())),
            None
        );
        // A signed chain compares its constants as signed values.
        let minus_one = u(u64::MAX);
        let signed = PureFactContext::new()
            .assume_condition(
                ConditionTerm::int64_signed_less_equal(a.clone(), b.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::int64_signed_less_equal(b.clone(), minus_one.clone()),
                true,
            );
        assert_eq!(
            signed.decide(&ConditionTerm::int64_signed_less_than(a.clone(), u(0))),
            Some(true)
        );
        assert_eq!(signed.decide(&lt(a.clone(), u(0))), Some(false));
    }

    #[test]
    fn uint64_constant_lower_bound_survives_checked_narrowing() {
        let value = Bitvector32Term::Variable(Variable(991003));
        let context = PureFactContext::new()
            .assume_condition(
                ConditionTerm::uint64_less_than(Bitvector32Term::UInt64Constant(0), value.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::uint64_less_equal(
                    value.clone(),
                    Bitvector32Term::UInt64Constant(i32::MAX as u64),
                ),
                true,
            );
        let goal = ConditionTerm::signed_less_than(
            Bitvector32Term::Constant(0),
            Bitvector32Term::uint32_from_64(value),
        );
        assert_eq!(
            context.selected_for_test().decide_selected_condition(&goal),
            Some(true)
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../../scaling_tests/kernel/assumptions/condition_reasoning/order_paths/slice_index_tests.rs"
        );
    }
}

#[cfg(test)]
mod annotated_alignment_premise_tests {
    use super::*;

    #[test]
    fn alignment_certificates_cite_the_exact_annotated_premise() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer::symbolic(Variable(996_210));
        // Address annotations share identity. Keep the written stronger
        // premise for exact citation and withdraw it independently of a
        // weaker alignment premise.
        let source = ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: Box::new(Bitvector32Term::uint64_bitwise_and(
                Bitvector32Term::object_pointer_address(
                    pointer.clone(),
                    Some(CAccessClass::Scalar(CScalarClass::Int)),
                ),
                Bitvector32Term::UInt64Constant(7),
            )),
            right: Box::new(Bitvector32Term::UInt64Constant(0)),
        };
        assert_eq!(source, ConditionTerm::pointer_aligned(pointer.clone(), 8));
        let bare = ConditionTerm::pointer_aligned(pointer.clone(), 4);
        let context = PureFactContext::new().assume_condition(source.clone(), true);
        assert_eq!(
            context.pointer_alignment_certificate_decision(&pointer, 4),
            Some((true, Some(Proposition::ConditionIs(source.clone(), true))))
        );
        let both = context.assume_condition(bare.clone(), true);
        let remaining = both.without_exact_fact(&Proposition::ConditionIs(source, true));
        assert_eq!(
            remaining.pointer_alignment_certificate_decision(&pointer, 4),
            Some((true, Some(Proposition::ConditionIs(bare.clone(), true))))
        );
        assert_eq!(
            remaining
                .without_exact_fact(&Proposition::ConditionIs(bare, true))
                .pointer_alignment_certificate_decision(&pointer, 4),
            None
        );
    }
}

#[cfg(test)]
mod exact_order_path_tests {
    use super::*;

    fn var(index: u64) -> Bitvector32Term {
        Bitvector32Term::Variable(Variable(986_500 + index))
    }

    /// The walk as it was before the endpoint index: every node scans every
    /// order fact. The indexed walk must answer exactly as this does.
    fn scanned_order_path(
        context: &PureFactContext,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        require_strict: bool,
    ) -> bool {
        let order_facts = context.selected_for_test().condition_order_facts();
        let mut stack = vec![(left.clone(), false)];
        let mut seen = BTreeSet::new();
        while let Some((current, strict_so_far)) = stack.pop() {
            if !seen.insert((current.clone(), strict_so_far)) {
                continue;
            }
            let constant_connection = signed_bitvector_constant(&current)
                .zip(signed_bitvector_constant(right))
                .and_then(|(current, right)| (current <= right).then_some(current < right));
            if (&current == right || constant_connection.is_some())
                && (!require_strict || strict_so_far || constant_connection == Some(true))
            {
                return true;
            }
            for (edge_left, edge_right, edge_strict) in order_facts.iter() {
                let constant_connection = signed_bitvector_constant(&current)
                    .zip(signed_bitvector_constant(edge_left))
                    .and_then(|(current, edge_left)| {
                        (current <= edge_left).then_some(current < edge_left)
                    });
                if &current == edge_left || constant_connection.is_some() {
                    stack.push((
                        edge_right.clone(),
                        strict_so_far || *edge_strict || constant_connection == Some(true),
                    ));
                }
            }
        }
        false
    }

    struct Terms(u64);
    impl Terms {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1);
            self.0 >> 33
        }
        fn term(&mut self) -> Bitvector32Term {
            match self.next() % 5 {
                0 => Bitvector32Term::Constant((self.next() % 5) as u32),
                1 => Bitvector32Term::add(var(self.next() % 6), Bitvector32Term::Constant(1)),
                // A sum whose canonical form differs from its spelling, so
                // its facts are also filed under an alias key.
                2 => Bitvector32Term::add(Bitvector32Term::Constant(1), var(self.next() % 6)),
                _ => var(self.next() % 6),
            }
        }
    }

    #[test]
    fn indexed_walk_agrees_with_scanning_every_order_fact() {
        let _session = crate::kernel::VerificationSession::enter();
        for seed in 0..30u64 {
            let mut terms = Terms(seed + 1);
            let mut context = PureFactContext::new();
            for _ in 0..14 {
                let (left, right) = (Box::new(terms.term()), Box::new(terms.term()));
                let condition = match terms.next() % 4 {
                    0 => ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left,
                        right,
                    },
                    1 => ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessEqual,
                        left,
                        right,
                    },
                    2 => ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterThan,
                        left,
                        right,
                    },
                    _ => ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterEqual,
                        left,
                        right,
                    },
                };
                context = context.assume_condition(condition, !terms.next().is_multiple_of(3));
            }
            for _ in 0..40 {
                let (left, right) = (terms.term(), terms.term());
                let strict = terms.next().is_multiple_of(2);
                assert_eq!(
                    context.has_exact_order_path(&left, &right, strict),
                    scanned_order_path(&context, &left, &right, strict),
                    "seed {seed}: {left:?} to {right:?}, strict {strict}"
                );
            }
        }
    }

    /// The evidence walk as it was before `OrderFactsByLower`: every node
    /// visits every order fact, in reverse fact order.
    fn scanned_order_path_evidence(
        context: &PureFactContext,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        require_strict: bool,
    ) -> Option<Vec<SignedOrderDerivationStep>> {
        let order_facts = context
            .condition_facts
            .iter()
            .filter_map(|(condition, value)| {
                condition_as_order_fact(condition, *value).map(|(lower, upper, strict)| {
                    SignedOrderDerivationStep {
                        lower,
                        upper,
                        strict,
                        premise: Proposition::ConditionIs(condition.clone(), *value),
                    }
                })
            })
            .collect::<Vec<_>>();
        let mut stack = vec![(left.clone(), false, Vec::new())];
        let mut seen = BTreeSet::new();
        while let Some((current, strict_so_far, path)) = stack.pop() {
            if !seen.insert((current.clone(), strict_so_far)) {
                continue;
            }
            let constant_connection = signed_bitvector_constant(&current)
                .zip(signed_bitvector_constant(right))
                .and_then(|(current, right)| (current <= right).then_some(current < right));
            if (&current == right || constant_connection.is_some())
                && (!require_strict || strict_so_far || constant_connection == Some(true))
                && !path.is_empty()
            {
                return Some(path);
            }
            for edge in order_facts.iter().rev() {
                let constant_connection = signed_bitvector_constant(&current)
                    .zip(signed_bitvector_constant(&edge.lower))
                    .and_then(|(current, edge_left)| {
                        (current <= edge_left).then_some(current < edge_left)
                    });
                if current != edge.lower && constant_connection.is_none() {
                    continue;
                }
                let mut extended = path.clone();
                extended.push(edge.clone());
                stack.push((
                    edge.upper.clone(),
                    strict_so_far || edge.strict || constant_connection == Some(true),
                    extended,
                ));
            }
        }
        None
    }

    /// The indexed evidence walk returns the very path the full scan did,
    /// not only an answer of the same truth.
    #[test]
    fn indexed_evidence_walk_finds_the_scanned_path() {
        let _session = crate::kernel::VerificationSession::enter();
        for seed in 0..30u64 {
            let mut terms = Terms(seed + 101);
            let mut context = PureFactContext::new();
            for _ in 0..14 {
                let (left, right) = (Box::new(terms.term()), Box::new(terms.term()));
                let condition = match terms.next() % 4 {
                    0 => ConditionTerm::Compare {
                        format: crate::kernel::MachineIntegerType::Int32,
                        relation: crate::kernel::CompareRelation::LessThan,
                        left,
                        right,
                    },
                    1 => ConditionTerm::Compare {
                        format: crate::kernel::MachineIntegerType::Int32,
                        relation: crate::kernel::CompareRelation::LessEqual,
                        left,
                        right,
                    },
                    2 => ConditionTerm::Compare {
                        format: crate::kernel::MachineIntegerType::Int32,
                        relation: crate::kernel::CompareRelation::GreaterThan,
                        left,
                        right,
                    },
                    _ => ConditionTerm::Compare {
                        format: crate::kernel::MachineIntegerType::Int32,
                        relation: crate::kernel::CompareRelation::GreaterEqual,
                        left,
                        right,
                    },
                };
                context = context.assume_condition(condition, !terms.next().is_multiple_of(3));
            }
            for _ in 0..40 {
                let (left, right) = (terms.term(), terms.term());
                let strict = terms.next().is_multiple_of(2);
                let indexed = context
                    .exact_signed_order_path_evidence(&left, &right, strict)
                    .map(|path| {
                        path.into_iter()
                            .map(|step| step.premise)
                            .collect::<Vec<_>>()
                    });
                let scanned =
                    scanned_order_path_evidence(&context, &left, &right, strict).map(|path| {
                        path.into_iter()
                            .map(|step| step.premise)
                            .collect::<Vec<_>>()
                    });
                assert_eq!(
                    indexed, scanned,
                    "seed {seed}: {left:?} to {right:?}, strict {strict}"
                );
            }
        }
    }

    /// A walk from a constant reads the order facts from a constant at
    /// least as large, not every order fact. Both walks once collected every
    /// order fact, so their work grew with unrelated bounds.
    #[test]
    fn constant_order_walks_ignore_unrelated_order_facts() {
        let _session = crate::kernel::VerificationSession::enter();
        let mut samples = Vec::new();
        for size in [16u64, 64, 256] {
            let mut context = PureFactContext::new()
                .assume_condition(ConditionTerm::signed_less_than(5u32.into(), var(0)), true);
            for index in 0..size {
                context = context.assume_condition(
                    ConditionTerm::signed_less_than(var(10 + 2 * index), var(11 + 2 * index)),
                    true,
                );
            }
            let (found, walk) = crate::instrumentation::measure_deterministic_work(|| {
                context.has_exact_order_path(&3u32.into(), &var(0), true)
            });
            assert!(found);
            let (evidence, evidence_work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    context.exact_signed_order_path_evidence(&3u32.into(), &var(0), true)
                });
            assert!(evidence.is_some());
            samples.push((walk, evidence_work));
        }
        assert!(
            samples.windows(2).all(|pair| pair[0] == pair[1]),
            "unrelated order facts changed a constant walk's work: {samples:?}"
        );
    }

    /// An order chain of fixed length beside many unrelated order facts:
    /// the walk follows the chain's edges only.
    #[test]
    fn exact_order_path_ignores_unrelated_order_facts() {
        let _session = crate::kernel::VerificationSession::enter();
        let work_beside = |unrelated: u64| {
            let mut context = PureFactContext::new();
            for index in 0..8 {
                context = context.assume_condition(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left: Box::new(var(index)),
                        right: Box::new(var(index + 1)),
                    },
                    true,
                );
            }
            for index in 0..unrelated {
                context = context.assume_condition(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left: Box::new(var(1_000 + 2 * index)),
                        right: Box::new(var(1_001 + 2 * index)),
                    },
                    true,
                );
            }
            let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.has_exact_order_path(&var(0), &var(8), true)
            });
            assert!(found);
            work
        };
        let small = work_beside(16);
        let large = work_beside(1_024);
        // The walk charges the nodes and edges it visits.
        assert!(small > 0);
        assert_eq!(
            large, small,
            "the walk cost {large} beside 1,024 facts and {small} beside 16"
        );
    }
}
