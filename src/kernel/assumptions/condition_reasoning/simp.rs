use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

/// Only these operand families are compared up to memory resolution.
/// Every other condition is matched by its exact fact identity. The index
/// and the matcher share this classification so an exact-only refusal cannot
/// silently omit a family that the matcher knows how to relate.
enum MemoryMatchOperands<'a> {
    Words(
        MachineIntegerType,
        CompareRelation,
        &'a Bitvector32Term,
        &'a Bitvector32Term,
    ),
    Offsets(&'a PointerOffsetTerm, &'a PointerOffsetTerm),
    Exact,
}

fn memory_match_operands(condition: &ConditionTerm) -> MemoryMatchOperands<'_> {
    match condition {
        ConditionTerm::Compare {
            format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
            relation,
            left,
            right,
        } => MemoryMatchOperands::Words(*format, *relation, left, right),
        ConditionTerm::PointerOffsetEqual(left, right) => MemoryMatchOperands::Offsets(left, right),
        _ => MemoryMatchOperands::Exact,
    }
}

impl PureFactContext {
    pub(crate) fn decide_condition_for_simp(&self, condition: &ConditionTerm) -> Option<bool> {
        if let Some(value) = self.known_condition_value(condition) {
            return Some(value);
        }
        if let Some(value) = self
            .decide_small_uint64_index_order(condition)
            .or_else(|| self.decide_indexed_greater_equal(condition))
            .or_else(|| self.decide_masked_order(condition))
            .or_else(|| self.decide_widened_sum_bound(condition))
        {
            return Some(value);
        }
        if let Some(value) = self.decide_exact_signed_constant_order(condition) {
            return Some(value);
        }

        if matches!(condition, ConditionTerm::PointerValueEqual(..)) {
            return self.decide(condition);
        }
        match condition {
            ConditionTerm::AlgebraicEqual(left, right) => {
                self.decide_algebraic_equality(left, right)
            }
            ConditionTerm::Constant(value) => Some(*value),
            ConditionTerm::PointerEqual(left, right) if left == right => Some(true),
            ConditionTerm::PointerEqual(left, right) if self.pointers_known_equal(left, right) => {
                Some(true)
            }
            ConditionTerm::PointerEqual(left, right) if left.blocks_proven_distinct(right) => {
                Some(false)
            }
            ConditionTerm::PointerEqual(left, right) if left.block == right.block => self
                .decide_condition_for_simp(&ConditionTerm::pointer_offset_equal(
                    left.offset.clone(),
                    right.offset.clone(),
                )),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left,
                right,
            } if ConditionTerm::address_equality_as_pointer_equality(left, right).is_some() => {
                ConditionTerm::address_equality_as_pointer_equality(left, right)
                    .and_then(|condition| self.decide_condition_for_simp(&condition))
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: _,
                right: _,
            } if condition.as_pointer_alignment().is_some() => {
                let (pointer, alignment) = condition.as_pointer_alignment()?;
                self.decide_pointer_alignment(pointer, alignment)
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
                match (
                    self.wide_constant_from_equalities(left),
                    self.wide_constant_from_equalities(right),
                ) {
                    (Some(left), Some(right)) => Some(left == right),
                    _ => self.decide_uint64_equality_extras(left, right),
                }
            }
            ConditionTerm::PointerOffsetEqual(left, right) => {
                if self.equality_graph.are_offsets_equal(left, right)
                    || pointer_offsets_proven_equal_for_memory_resolution(left, right, self)
                {
                    Some(true)
                } else {
                    match (left.as_ref().as_const(), right.as_ref().as_const()) {
                        (Some(left), Some(right)) => Some(left == right),
                        _ => None,
                    }
                }
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            } => {
                let narrowed_constant = |term: &Bitvector32Term| match term {
                    Bitvector32Term::UInt32From64(wide) => self
                        .wide_constant_from_equalities(wide)
                        .map(|bits| bits as u32),
                    Bitvector32Term::Constant(bits) | Bitvector32Term::UInt32Constant(bits) => {
                        Some(*bits)
                    }
                    _ => None,
                };
                if let (Some(left), Some(right)) =
                    (narrowed_constant(left), narrowed_constant(right))
                {
                    return Some(left == right);
                }
                if bitvector_terms_proven_equal_for_memory_resolution(left, right, self)
                    || self.proves_condition_from_facts_for_simp(condition, true)
                {
                    Some(true)
                } else if bitvector_same_base_nonzero_const_offset(left, right) {
                    Some(false)
                } else {
                    None
                }
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            } if self.increment_preserves_order_for_simp(left, right) => Some(true),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            } if left.as_ref().add_const_base(1).is_some_and(|base| {
                self.exact_condition_value(&ConditionTerm::signed_less_than(
                    base,
                    right.as_ref().clone(),
                )) == Some(true)
            }) =>
            {
                Some(true)
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            } if self.exact_condition_value(&ConditionTerm::signed_less_than(
                left.as_ref().clone(),
                Bitvector32Term::Add(
                    Box::new(right.as_ref().clone()),
                    Box::new(Bitvector32Term::Constant(1)),
                ),
            )) == Some(true)
                && self.has_exact_bitvector_inequality_after_cancellation(left, right) =>
            {
                Some(true)
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            } if self.positive_offset_is_proven_above_for_simp(left, right) => Some(true),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left,
                right,
            } if right.as_ref() == &Bitvector32Term::Constant(0)
                && left.as_ref().subtract_one_base().is_some_and(|base| {
                    self.exact_condition_value(&ConditionTerm::signed_greater_than(
                        base,
                        Bitvector32Term::Constant(0),
                    )) == Some(true)
                }) =>
            {
                Some(true)
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            } if left.as_ref() == &Bitvector32Term::Constant(0)
                && right.as_ref().subtract_one_base().is_some_and(|base| {
                    self.exact_condition_value(&ConditionTerm::signed_greater_than(
                        base,
                        Bitvector32Term::Constant(0),
                    )) == Some(true)
                }) =>
            {
                Some(true)
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            } if left.as_ref().subtract_one_base().is_some_and(|base| {
                &base == right.as_ref()
                    && self.exact_condition_value(&ConditionTerm::signed_greater_than(
                        base,
                        Bitvector32Term::Constant(0),
                    )) == Some(true)
            }) =>
            {
                Some(true)
            }
            _ => {
                if self.proves_condition_from_facts_for_simp(condition, true) {
                    return Some(true);
                }
                if self.proves_condition_from_facts_for_simp(condition, false) {
                    return Some(false);
                }
                // This stronger normalization is tactic-local. Keep its atomic
                // checks structural: calling the general condition solver here
                // can recurse through fact transport and memory alias solving.
                if let Some((left, right, strict)) = condition_as_order_fact(condition, true)
                    && self.has_order_path_for_simp(&left, &right, strict)
                {
                    return Some(true);
                }
                if let Some((left, right, strict)) = condition_as_order_fact(condition, false)
                    && self.has_order_path_for_simp(&left, &right, strict)
                {
                    return Some(false);
                }
                if condition_as_order_fact(condition, true).is_some() {
                    Self::decide_intrinsically(condition)
                } else {
                    self.decide(condition)
                }
            }
        }
    }

    fn increment_preserves_order_for_simp(
        &self,
        incremented_lower: &Bitvector32Term,
        incremented_value: &Bitvector32Term,
    ) -> bool {
        let order_facts = self.condition_order_facts();
        order_facts.iter().any(|(lower, value, strict)| {
            if *strict
                || Bitvector32Term::add(lower.clone(), Bitvector32Term::Constant(1))
                    != *incremented_lower
                || Bitvector32Term::add(value.clone(), Bitvector32Term::Constant(1))
                    != *incremented_value
            {
                return false;
            }
            order_facts
                .iter()
                .any(|(strict_value, _, strict)| *strict && strict_value == value)
        })
    }

    fn has_exact_bitvector_inequality_after_cancellation(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        self.exact_condition_value(&ConditionTerm::equal(left.clone(), right.clone()))
            == Some(false)
            || self
                .condition_facts
                .scan_for_search()
                .any(|(condition, value)| {
                    if *value {
                        return false;
                    }
                    let ConditionTerm::Compare {
                        format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                        relation: CompareRelation::Equal,
                        left: fact_left,
                        right: fact_right,
                    } = condition
                    else {
                        return false;
                    };
                    let Some((fact_left, fact_right)) =
                        bitvector_equality_after_additive_cancellation(fact_left, fact_right)
                    else {
                        return false;
                    };
                    (&fact_left == left && &fact_right == right)
                        || (&fact_left == right && &fact_right == left)
                })
    }

    fn decide_condition_for_simp_without_prop_facts(
        &self,
        condition: &ConditionTerm,
    ) -> Option<bool> {
        if let Some(value) = self.known_condition_value(condition) {
            return Some(value);
        }
        if let Some(value) = self
            .decide_small_uint64_index_order(condition)
            .or_else(|| self.decide_indexed_greater_equal(condition))
            .or_else(|| self.decide_masked_order(condition))
            .or_else(|| self.decide_widened_sum_bound(condition))
        {
            return Some(value);
        }
        if let Some(value) = self.decide_exact_signed_constant_order(condition) {
            return Some(value);
        }
        if let ConditionTerm::Constant(value) = condition {
            return Some(*value);
        }
        if let ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left,
            right,
        } = condition
            && self.exact_condition_value(&ConditionTerm::signed_less_than(
                left.as_ref().clone(),
                Bitvector32Term::Add(
                    Box::new(right.as_ref().clone()),
                    Box::new(Bitvector32Term::Constant(1)),
                ),
            )) == Some(true)
            && self.has_exact_bitvector_inequality_after_cancellation(left, right)
        {
            return Some(true);
        }
        if let Some((left, right, strict)) = condition_as_order_fact(condition, true)
            && self.has_order_path_for_simp(&left, &right, strict)
        {
            return Some(true);
        }
        if let Some((left, right, strict)) = condition_as_order_fact(condition, false)
            && self.has_order_path_for_simp(&left, &right, strict)
        {
            return Some(false);
        }
        Self::decide_intrinsically(condition)
    }

    fn proves_condition_from_facts_for_simp(&self, condition: &ConditionTerm, value: bool) -> bool {
        let Some(_proof) = SimpFactReasoningGuard::enter(condition, value) else {
            return false;
        };
        // A slow-part scan: only `simp` reaches this, and a certificate
        // runs it again over the step's retained premises alone.
        self.condition_facts
            .scan_for_search()
            .any(|(fact, fact_value)| {
                *fact_value == value && self.condition_matches_for_simp(fact, condition)
            })
            || self.prop_facts.scan_for_search().any(|proposition| {
                self.proposition_proves_condition_for_simp(proposition, condition, value)
            })
    }

    pub(in crate::kernel) fn has_matching_condition_fact_for_memory_resolution(
        &self,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        let Some(indexed) =
            self.indexed_matching_condition_fact_for_memory_resolution(condition, value)
        else {
            return self.scanned_matching_condition_fact_for_memory_resolution(condition, value);
        };
        #[cfg(debug_assertions)]
        crate::instrumentation::uncharged_debug_check(|| {
            let scanned = crate::kernel::assumptions::without_reasoning_provenance(|| {
                self.scanned_matching_condition_fact_for_memory_resolution(condition, value)
            });
            assert_eq!(
                indexed, scanned,
                "the indexed memory-resolution fact match disagrees with the full scan for \
                 {condition:?} = {value}"
            );
        });
        indexed
    }

    fn scanned_matching_condition_fact_for_memory_resolution(
        &self,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        self.condition_facts
            .scan_unindexed()
            .any(|(fact, fact_value)| {
                crate::instrumentation::record_deterministic_work(1);
                *fact_value == value && self.condition_matches_for_simp(fact, condition)
            })
    }

    /// The memory-resolution match read from the condition-match index
    /// instead of a scan of every condition fact, or `None` where the index
    /// cannot be shown to hold every fact the scan could match.
    ///
    /// Every exact hit is a direct lookup. `MemoryMatchOperands::Exact` kinds
    /// can only match by identity, so their misses are direct lookups too.
    /// Compound queries first ask the facts under their canonical key. A
    /// successful memory match closes them; a miss retains the scan, since
    /// other memory-equivalent spellings may have different canonical keys.
    /// The remaining families pair sides by memory-resolution equality. For a query
    /// whose sides are both atoms (a constant, or a variable no load names),
    /// an atom side of a fact is memory-resolution equal to a query side only
    /// by identity, through the equality graph, by an exact constant pin
    /// (itself an equality-graph edge), or through an exact
    /// `PointerOffsetEqual` fact of their byte scalings; those are the
    /// spellings read here. A fact with a non-atom side is filed among the
    /// family's open facts and is always asked. The 64-bit equalities pin a
    /// term to a constant outside the 32-bit equality graph. Only sources
    /// naming a selected scalar spelling require the ordinary fallback. Debug builds compare every indexed
    /// answer with the scan.
    fn indexed_matching_condition_fact_for_memory_resolution(
        &self,
        condition: &ConditionTerm,
        value: bool,
    ) -> Option<bool> {
        use crate::kernel::primitives::ConditionMatchKey;
        // An exact hit needs no operand reasoning, even for loads and sums.
        // For exact-only kinds a miss is conclusive too: no other condition
        // can match under `condition_matches_for_simp`.
        crate::instrumentation::record_deterministic_work(1);
        let exact = self.condition_facts.get(condition) == Some(&value);
        if exact || matches!(memory_match_operands(condition), MemoryMatchOperands::Exact) {
            return Some(exact);
        }
        // The matcher also accepts a fixed number of syntactic symmetries.
        // Probe those exact keys before resolving operands or scanning facts.
        let lookup = |candidate: ConditionTerm| {
            crate::instrumentation::record_deterministic_work(1);
            self.condition_facts.get(&candidate) == Some(&value)
        };
        let symmetric_hit = match memory_match_operands(condition) {
            MemoryMatchOperands::Words(format, relation, left, right) => {
                use CompareRelation::*;
                let reversed = match relation {
                    Equal => Equal,
                    LessThan => GreaterThan,
                    LessEqual => GreaterEqual,
                    GreaterThan => LessThan,
                    GreaterEqual => LessEqual,
                };
                // Condition identity already ignores signedness for 32-bit
                // equality; order comparisons retain their exact carrier.
                lookup(ConditionTerm::Compare {
                    format,
                    relation: reversed,
                    left: Box::new(right.clone()),
                    right: Box::new(left.clone()),
                })
            }
            MemoryMatchOperands::Offsets(left, right) => lookup(ConditionTerm::PointerOffsetEqual(
                Box::new(right.clone()),
                Box::new(left.clone()),
            )),
            MemoryMatchOperands::Exact => unreachable!("exact-only kinds returned above"),
        };
        if symmetric_hit {
            return Some(true);
        }
        let atom = |term: &Bitvector32Term| match term {
            Bitvector32Term::Constant(_) | Bitvector32Term::UInt32Constant(_) => true,
            Bitvector32Term::Variable(variable) => {
                crate::kernel::eval::registered_load_for_variable(variable).is_none()
            }
            _ => false,
        };
        let key = crate::kernel::assumptions::condition_match_key(condition)?;
        let matches = |facts: &crate::persistent::PersistentMap<ConditionTerm, bool>| {
            facts.iter().any(|(fact, fact_value)| {
                crate::instrumentation::record_deterministic_work(1);
                *fact_value == value && self.condition_matches_for_simp(fact, condition)
            })
        };
        let atom_query = matches!(
            memory_match_operands(condition),
            MemoryMatchOperands::Words(_, _, left, right) if atom(left) && atom(right)
        );
        if !atom_query {
            // Loads and their registered variables (including inside sums
            // and scaled offsets) share a canonical key. It selects candidates,
            // not a verdict: retain the memory matcher's snapshot checks.
            crate::instrumentation::record_deterministic_work(1);
            // A miss is inconclusive: other memory-equivalent spellings may
            // live under different keys, so the caller retains its fallback.
            return self
                .condition_facts_by_sides
                .get(&key)
                .is_some_and(matches)
                .then_some(true);
        }
        let spellings = |term: &Bitvector32Term| {
            let mut terms = BTreeSet::from([term.clone()]);
            terms.extend(self.bitvector_equality_class(term));
            for byte_width in [1, 4] {
                let scaled = PointerOffsetTerm::scale_int32(term.clone(), byte_width);
                crate::instrumentation::record_deterministic_work(1);
                if let Some(aliases) = self.equality_graph.exact_offset_aliases(&scaled) {
                    for alias in aliases.iter() {
                        crate::instrumentation::record_deterministic_work(1);
                        if let PointerOffsetTerm::Int32Scaled { value, .. } = alias
                            && PointerOffsetTerm::scale_int32(value.as_ref().clone(), byte_width)
                                == *alias
                        {
                            terms.insert(value.as_ref().clone());
                        }
                    }
                }
            }
            terms
        };
        let (left, right) = match &key {
            ConditionMatchKey::Equal(left, right)
            | ConditionMatchKey::Order(_, left, right)
            | ConditionMatchKey::UnsignedOrder(_, left, right) => (left, right),
            ConditionMatchKey::OffsetEqual(_, _) | ConditionMatchKey::OverflowAdd(_, _) => {
                return None;
            }
        };
        let right_spellings = spellings(right);
        let left_spellings = spellings(left);
        if left_spellings
            .iter()
            .chain(&right_spellings)
            .any(|term| self.equality_graph.has_uint64_source(term))
        {
            return None;
        }
        let keys = self.condition_match_keys_for_spellings(
            &key,
            &left_spellings,
            &right_spellings,
            || crate::instrumentation::record_deterministic_work(1),
        );
        Some(
            keys.iter().any(|key| {
                crate::instrumentation::record_deterministic_work(1);
                self.condition_facts_by_sides.get(key).is_some_and(matches)
            }) || self
                .open_condition_facts
                .get(&key.family())
                .is_some_and(matches),
        )
    }

    pub(in crate::kernel) fn has_anchored_bitvector_equality_fact_for_memory_resolution(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        // An anchored fact has `left` or `right` itself as a side.
        let mut candidates = self.condition_facts_with_side(left);
        candidates.extend(self.condition_facts_with_side(right));
        candidates.sort_unstable_by(|first, second| first.0.cmp(second.0));
        candidates.dedup_by(|first, second| first.0 == second.0);
        candidates.into_iter().any(|(fact, value)| {
            let (
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal,
                    left: fact_left,
                    right: fact_right,
                },
                true,
            ) = (fact, value)
            else {
                return false;
            };
            let anchored = fact_left.as_ref() == left
                || fact_left.as_ref() == right
                || fact_right.as_ref() == left
                || fact_right.as_ref() == right;
            anchored
                && self.condition_matches_for_simp(
                    fact,
                    &ConditionTerm::equal(left.clone(), right.clone()),
                )
        })
    }

    fn proposition_proves_condition_for_simp(
        &self,
        proposition: &Proposition,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        match proposition {
            Proposition::ConditionIs(fact, fact_value) => {
                *fact_value == value && self.condition_matches_for_simp(fact, condition)
            }
            Proposition::And(left, right) => {
                self.proposition_proves_condition_for_simp(left, condition, value)
                    || self.proposition_proves_condition_for_simp(right, condition, value)
            }
            Proposition::Implies(left, right) => {
                // Reject implications whose conclusion cannot establish the
                // target before proving their (potentially expensive)
                // antecedent against the whole context.
                self.proposition_proves_condition_for_simp(right, condition, value)
                    && self.proves_proposition_for_simp_without_search(left)
            }
            Proposition::ForAll { body, .. } => {
                self.proposition_proves_condition_for_simp(body, condition, value)
                    || self
                        .forall_instantiations_for_condition(proposition, condition)
                        .iter()
                        .any(|instance| {
                            self.proposition_proves_condition_for_simp(instance, condition, value)
                        })
            }
            _ => false,
        }
    }

    fn proves_proposition_for_simp_without_search(&self, proposition: &Proposition) -> bool {
        if solve_builtin_prop(proposition) {
            return true;
        }
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                self.decide_condition_for_simp_without_prop_facts(condition) == Some(*value)
            }
            Proposition::And(left, right) => {
                self.proves_proposition_for_simp_without_search(left)
                    && self.proves_proposition_for_simp_without_search(right)
            }
            Proposition::Not(body) => match body.as_ref() {
                Proposition::ConditionIs(condition, value) => {
                    self.decide_condition_for_simp_without_prop_facts(condition) == Some(!*value)
                }
                _ => self.prop_facts.contains(proposition),
            },
            _ => self.proves_exact(proposition),
        }
    }

    fn condition_matches_for_simp(&self, fact: &ConditionTerm, target: &ConditionTerm) -> bool {
        if fact == target {
            return true;
        }
        use MemoryMatchOperands::{Exact, Offsets, Words};
        match (memory_match_operands(fact), memory_match_operands(target)) {
            (
                Words(_, CompareRelation::Equal, fl, fr),
                Words(_, CompareRelation::Equal, tl, tr),
            ) => {
                bitvector_terms_proven_equal_for_memory_resolution(fl, tl, self)
                    && bitvector_terms_proven_equal_for_memory_resolution(fr, tr, self)
                    || bitvector_terms_proven_equal_for_memory_resolution(fl, tr, self)
                        && bitvector_terms_proven_equal_for_memory_resolution(fr, tl, self)
            }
            (Offsets(fl, fr), Offsets(tl, tr)) => {
                pointer_offsets_proven_equal_for_memory_resolution(fl, tl, self)
                    && pointer_offsets_proven_equal_for_memory_resolution(fr, tr, self)
                    || pointer_offsets_proven_equal_for_memory_resolution(fl, tr, self)
                        && pointer_offsets_proven_equal_for_memory_resolution(fr, tl, self)
            }
            (Words(ff, frel, fl, fr), Words(tf, trel, tl, tr)) if ff == tf => {
                if frel == trel {
                    bitvector_terms_proven_equal_for_memory_resolution(fl, tl, self)
                        && bitvector_terms_proven_equal_for_memory_resolution(fr, tr, self)
                } else if matches!(
                    (frel, trel),
                    (CompareRelation::LessThan, CompareRelation::GreaterThan)
                        | (CompareRelation::GreaterThan, CompareRelation::LessThan)
                        | (CompareRelation::LessEqual, CompareRelation::GreaterEqual)
                        | (CompareRelation::GreaterEqual, CompareRelation::LessEqual)
                ) {
                    bitvector_terms_proven_equal_for_memory_resolution(fl, tr, self)
                        && bitvector_terms_proven_equal_for_memory_resolution(fr, tl, self)
                } else {
                    false
                }
            }
            (Exact, _) | (_, Exact) => false,
            _ => false,
        }
    }

    fn has_order_path_for_simp(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        require_strict: bool,
    ) -> bool {
        let mut order_facts = self.condition_order_facts().as_ref().clone();
        self.collect_quantified_order_facts_for_condition(
            &ConditionTerm::signed_less_than(left.clone(), right.clone()),
            &mut order_facts,
        );
        let mut stack = vec![(left.clone(), false)];
        let mut seen = BTreeSet::new();
        while let Some((current, strict_so_far)) = stack.pop() {
            if !seen.insert((current.clone(), strict_so_far)) {
                continue;
            }
            if let Some(connection_strict) = self.order_path_connection_for_simp(&current, right)
                && (!require_strict || strict_so_far || connection_strict)
            {
                return true;
            }
            for (edge_left, edge_right, edge_strict) in order_facts.iter() {
                if let Some(connection_strict) =
                    self.order_path_connection_for_simp(&current, edge_left)
                {
                    stack.push((
                        edge_right.clone(),
                        strict_so_far || connection_strict || *edge_strict,
                    ));
                }
            }
        }
        false
    }

    fn positive_offset_is_proven_above_for_simp(
        &self,
        base: &Bitvector32Term,
        term: &Bitvector32Term,
    ) -> bool {
        let Some((term_base, addend)) = term.add_const_parts() else {
            return false;
        };
        if !self.bitvector_terms_equal_for_simp(&term_base, base)
            || nonnegative_int32_value(addend).is_none_or(|value| value <= 0)
        {
            return false;
        }
        // A strict upper bound by any int32 value proves that `base` is below
        // INT_MAX. Therefore adding one cannot wrap. Keep this simp rule
        // syntactic so certificate selection cannot recurse into memory or
        // alias resolution.
        addend == 1
            && self.condition_facts.scan_for_search().any(|(condition, value)| {
                matches!(
                    (condition, value),
                    (
                        ConditionTerm::Compare { format: MachineIntegerType::Int32, relation: CompareRelation::LessThan, left, right: _ },
                        true
                    ) if self.bitvector_terms_equal_for_simp(left, base)
                ) || matches!(
                    (condition, value),
                    (
                        ConditionTerm::Compare { format: MachineIntegerType::Int32, relation: CompareRelation::GreaterThan, left: _, right },
                        true
                    ) if self.bitvector_terms_equal_for_simp(right, base)
                )
            })
    }

    /// The unique constant this term resolves to through equality facts
    /// (with per-load snapshot bridging), if any. Bounded and fuel-free.
    pub(in crate::kernel) fn known_signed_constant_after_normalization(
        &self,
        term: &Bitvector32Term,
    ) -> Option<i64> {
        self.signed_constant_after_equality_normalization(term)
    }

    fn order_path_connection_for_simp(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> Option<bool> {
        if self.bitvector_terms_equal_for_simp(left, right) {
            return Some(false);
        }
        if self.positive_offset_is_proven_above_for_simp(left, right) {
            return Some(true);
        }
        let left = self.signed_constant_after_equality_normalization(left)?;
        let right = self.signed_constant_after_equality_normalization(right)?;
        (left <= right).then_some(left < right)
    }

    fn bitvector_terms_equal_for_simp(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        if self.bitvector_terms_equal_for_transport(left, right) {
            return true;
        }

        self.condition_facts
            .scan_for_search()
            .any(|(condition, value)| {
                let (
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                        relation: CompareRelation::Equal,
                        left: fact_left,
                        right: fact_right,
                    },
                    true,
                ) = (condition, value)
                else {
                    return false;
                };
                self.bitvector_terms_equal_for_transport(left, fact_left)
                    && self.bitvector_terms_equal_for_transport(right, fact_right)
                    || self.bitvector_terms_equal_for_transport(left, fact_right)
                        && self.bitvector_terms_equal_for_transport(right, fact_left)
            })
    }
}

#[cfg(test)]
mod scaling_tests {
    use super::*;
    include!("../../../scaling_tests/kernel/assumptions/condition_reasoning/simp.rs");
}

#[cfg(test)]
mod memory_condition_match_tests {
    use super::*;

    fn comparison(
        format: MachineIntegerType,
        relation: CompareRelation,
        left: u64,
        right: u64,
    ) -> ConditionTerm {
        ConditionTerm::Compare {
            format,
            relation,
            left: Box::new(Bitvector32Term::Variable(Variable(left))),
            right: Box::new(Bitvector32Term::Variable(Variable(right))),
        }
    }

    #[test]
    fn memory_condition_matching_keeps_reversed_orders_and_carriers() {
        use CompareRelation::*;
        use MachineIntegerType::*;
        let _session = crate::kernel::VerificationSession::enter();
        for format in [Int32, UInt32] {
            for (relation, reversed) in [
                (LessThan, GreaterThan),
                (LessEqual, GreaterEqual),
                (GreaterThan, LessThan),
                (GreaterEqual, LessEqual),
            ] {
                let context = PureFactContext::new()
                    .assume_condition(comparison(Int32, Equal, 960_000, 960_002), true)
                    .assume_condition(comparison(Int32, Equal, 960_001, 960_003), true)
                    .assume_condition(comparison(format, relation, 960_000, 960_001), true);
                assert!(context.has_matching_condition_fact_for_memory_resolution(
                    &comparison(format, reversed, 960_003, 960_002),
                    true
                ));
                let other_format = if format == Int32 { UInt32 } else { Int32 };
                assert!(!context.has_matching_condition_fact_for_memory_resolution(
                    &comparison(other_format, reversed, 960_003, 960_002),
                    true
                ));
            }
        }
        let words = PureFactContext::new()
            .assume_condition(comparison(Int32, Equal, 960_004, 960_005), true);
        assert!(words.has_matching_condition_fact_for_memory_resolution(
            &comparison(UInt32, Equal, 960_005, 960_004),
            true
        ));
        let offsets = ConditionTerm::pointer_offset_equal(
            PointerOffsetTerm::Variable(Variable(960_006)),
            PointerOffsetTerm::Variable(Variable(960_007)),
        );
        let reversed = ConditionTerm::pointer_offset_equal(
            PointerOffsetTerm::Variable(Variable(960_007)),
            PointerOffsetTerm::Variable(Variable(960_006)),
        );
        assert!(
            PureFactContext::new()
                .assume_condition(offsets, true)
                .has_matching_condition_fact_for_memory_resolution(&reversed, true)
        );
    }

    #[test]
    fn unsigned_memory_conditions_retain_open_facts_without_mixing_carriers() {
        let _session = crate::kernel::VerificationSession::enter();
        let var = |id| Bitvector32Term::Variable(Variable(id));
        let sum = Bitvector32Term::add(var(996_000), var(996_001));
        let base = PureFactContext::new()
            .assume_condition(ConditionTerm::equal(var(996_001), 0u32.into()), true);
        let goal = ConditionTerm::unsigned_less_than(var(996_000), var(996_002));
        for value in [false, true] {
            let source = ConditionTerm::unsigned_less_than(sum.clone(), var(996_002));
            let held = base.clone().assume_condition(source.clone(), value);
            assert_eq!(
                held.indexed_matching_condition_fact_for_memory_resolution(&goal, value),
                Some(true)
            );
            assert!(held.has_matching_condition_fact_for_memory_resolution(&goal, value));
            let withdrawn = held.without_exact_fact(&Proposition::ConditionIs(source, value));
            assert!(!withdrawn.has_matching_condition_fact_for_memory_resolution(&goal, value));
            let signed = base.clone().assume_condition(
                ConditionTerm::signed_less_than(sum.clone(), var(996_002)),
                value,
            );
            assert!(!signed.has_matching_condition_fact_for_memory_resolution(&goal, value));
        }
    }

    #[test]
    fn compound_memory_condition_candidates_preserve_snapshots_and_withdrawal() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = CMemory::new();
        let pointer = Pointer::symbolic(Variable(999_000));
        let load = |memory: &CMemory| {
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory_ref(memory),
                Box::new(pointer.clone()),
                crate::kernel::LoadKind::Int32,
            )
        };
        let raw = load(&memory);
        let named =
            Bitvector32Term::Variable(crate::kernel::eval::load_variable_for_term(&raw).unwrap().0);
        let changed = memory
            .clone()
            .store(pointer.clone(), CValue::Int32(9u32.into()));
        let condition = |kind, term| {
            let left = Bitvector32Term::add(term, 1u32.into());
            let right = Bitvector32Term::Variable(Variable(999_001));
            match kind {
                0 => ConditionTerm::signed_less_than(left, right),
                1 => ConditionTerm::unsigned_less_than(left, right),
                _ => ConditionTerm::pointer_offset_equal(
                    PointerOffsetTerm::scale_int32(left, 4),
                    PointerOffsetTerm::scale_int32(right, 4),
                ),
            }
        };
        for kind in 0..3 {
            let source = condition(kind, named.clone());
            let goal = condition(kind, raw.clone());
            for value in [false, true] {
                let held = PureFactContext::new().assume_condition(source.clone(), value);
                assert_eq!(
                    held.indexed_matching_condition_fact_for_memory_resolution(&goal, value),
                    Some(true)
                );
                assert!(held.has_matching_condition_fact_for_memory_resolution(&goal, value));
                assert!(!held.has_matching_condition_fact_for_memory_resolution(&goal, !value));
                assert!(!held.has_matching_condition_fact_for_memory_resolution(
                    &condition(kind, load(&changed)),
                    value
                ));
                let withdrawn =
                    held.without_exact_fact(&Proposition::ConditionIs(source.clone(), value));
                assert!(!withdrawn.has_matching_condition_fact_for_memory_resolution(&goal, value));
            }
        }
    }

    #[test]
    fn exact_memory_condition_matching_respects_truth_and_withdrawal() {
        let _session = crate::kernel::VerificationSession::enter();
        let goal = comparison(
            MachineIntegerType::UInt64,
            CompareRelation::LessThan,
            960_010,
            960_011,
        );
        let parent = PureFactContext::new().assume_condition(goal.clone(), true);
        let child = parent.without_exact_fact(&Proposition::ConditionIs(goal.clone(), true));
        assert!(parent.has_matching_condition_fact_for_memory_resolution(&goal, true));
        assert!(!parent.has_matching_condition_fact_for_memory_resolution(&goal, false));
        assert!(!child.has_matching_condition_fact_for_memory_resolution(&goal, true));
        let child = child.assume_condition(goal.clone(), false);
        assert!(child.has_matching_condition_fact_for_memory_resolution(&goal, false));
        assert!(!child.has_matching_condition_fact_for_memory_resolution(&goal, true));
        let reversed = comparison(
            MachineIntegerType::UInt64,
            CompareRelation::GreaterThan,
            960_011,
            960_010,
        );
        assert!(
            !parent.has_matching_condition_fact_for_memory_resolution(&reversed, true),
            "this matcher only transports 32-bit comparisons and offsets; wider conditions need exact identity"
        );
    }
}
