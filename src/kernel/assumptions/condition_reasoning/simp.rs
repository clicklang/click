use super::*;

impl PureFactContext {
    pub(crate) fn decide_condition_for_simp(&self, condition: &ConditionTerm) -> Option<bool> {
        if let Some(value) = self.exact_condition_value(condition) {
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
            ConditionTerm::Bitvector64Equal(left, right)
                if ConditionTerm::address_equality_as_pointer_equality(left, right).is_some() =>
            {
                ConditionTerm::address_equality_as_pointer_equality(left, right)
                    .and_then(|condition| self.decide_condition_for_simp(&condition))
            }
            ConditionTerm::Bitvector64Equal(_, _) if condition.as_pointer_alignment().is_some() => {
                let (pointer, alignment) = condition.as_pointer_alignment()?;
                self.decide_pointer_alignment(pointer, alignment)
            }
            ConditionTerm::Bitvector64Equal(left, right) => {
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
            ConditionTerm::Bitvector32Equal(left, right) => {
                let narrowed_constant = |term: &Bitvector32Term| match term {
                    Bitvector32Term::UInt32From64(wide) => self
                        .wide_constant_from_equalities(wide)
                        .map(|bits| bits as u32),
                    Bitvector32Term::Constant(bits) => Some(*bits),
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
            ConditionTerm::Bitvector32SignedLessEqual(left, right)
                if self.increment_preserves_order_for_simp(left, right) =>
            {
                Some(true)
            }
            ConditionTerm::Bitvector32SignedLessEqual(left, right)
                if left.as_ref().add_const_base(1).is_some_and(|base| {
                    self.exact_condition_value(&ConditionTerm::signed_less_than(
                        base,
                        right.as_ref().clone(),
                    )) == Some(true)
                }) =>
            {
                Some(true)
            }
            ConditionTerm::Bitvector32SignedLessThan(left, right)
                if self.exact_condition_value(&ConditionTerm::signed_less_than(
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
            ConditionTerm::Bitvector32SignedLessThan(left, right)
                if self.positive_offset_is_proven_above_for_simp(left, right) =>
            {
                Some(true)
            }
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
                if right.as_ref() == &Bitvector32Term::Constant(0)
                    && left.as_ref().subtract_one_base().is_some_and(|base| {
                        self.exact_condition_value(&ConditionTerm::signed_greater_than(
                            base,
                            Bitvector32Term::Constant(0),
                        )) == Some(true)
                    }) =>
            {
                Some(true)
            }
            ConditionTerm::Bitvector32SignedLessEqual(left, right)
                if left.as_ref() == &Bitvector32Term::Constant(0)
                    && right.as_ref().subtract_one_base().is_some_and(|base| {
                        self.exact_condition_value(&ConditionTerm::signed_greater_than(
                            base,
                            Bitvector32Term::Constant(0),
                        )) == Some(true)
                    }) =>
            {
                Some(true)
            }
            ConditionTerm::Bitvector32SignedLessThan(left, right)
                if left.as_ref().subtract_one_base().is_some_and(|base| {
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
            || self.condition_facts.iter().any(|(condition, value)| {
                if *value {
                    return false;
                }
                let ConditionTerm::Bitvector32Equal(fact_left, fact_right) = condition else {
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
        if let Some(value) = self.exact_condition_value(condition) {
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
        if let ConditionTerm::Bitvector32SignedLessThan(left, right) = condition
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
        self.condition_facts.iter().any(|(fact, fact_value)| {
            *fact_value == value && self.condition_matches_for_simp(fact, condition)
        }) || self.prop_facts.iter().any(|proposition| {
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
        self.condition_facts.iter().any(|(fact, fact_value)| {
            crate::instrumentation::record_deterministic_work(1);
            *fact_value == value && self.condition_matches_for_simp(fact, condition)
        })
    }

    /// The memory-resolution match read from the condition-match index
    /// instead of a scan of every condition fact, or `None` where the index
    /// cannot be shown to hold every fact the scan could match.
    ///
    /// `condition_matches_for_simp` relates only facts of the query's kind
    /// family, pairing sides by memory-resolution equality. For a query
    /// whose sides are both atoms (a constant, or a variable no load names),
    /// an atom side of a fact is memory-resolution equal to a query side only
    /// by identity, through the equality graph, by an exact constant pin
    /// (itself an equality-graph edge), or through an exact
    /// `PointerOffsetEqual` fact of their byte scalings; those are the
    /// spellings read here. A fact with a non-atom side is filed among the
    /// family's open facts and is always asked. The 64-bit equalities pin a
    /// term to a constant outside the 32-bit equality graph, so a context
    /// holding any is left to the scan. Debug builds compare every indexed
    /// answer with the scan.
    fn indexed_matching_condition_fact_for_memory_resolution(
        &self,
        condition: &ConditionTerm,
        value: bool,
    ) -> Option<bool> {
        use crate::kernel::primitives::ConditionMatchKey;
        let atom = |term: &Bitvector32Term| match term {
            Bitvector32Term::Constant(_) => true,
            Bitvector32Term::Variable(variable) => {
                crate::kernel::eval::registered_load_for_variable(variable).is_none()
            }
            _ => false,
        };
        let (left, right) = match condition {
            ConditionTerm::Bitvector32Equal(left, right)
            | ConditionTerm::Bitvector32SignedLessThan(left, right)
            | ConditionTerm::Bitvector32SignedLessEqual(left, right)
            | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
            | ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => (left, right),
            _ => return None,
        };
        if !atom(left) || !atom(right) || !self.bitvector64_equality_facts.is_empty() {
            return None;
        }
        let key = crate::kernel::assumptions::condition_match_key(condition)?;
        if self.condition_facts.get(condition) == Some(&value) {
            return Some(true);
        }
        let spellings = |term: &Bitvector32Term| {
            let mut terms = BTreeSet::from([term.clone()]);
            terms.extend(self.bitvector_equality_class(term));
            for byte_width in [1, 4] {
                let scaled = PointerOffsetTerm::scale_int32(term.clone(), byte_width);
                crate::instrumentation::record_deterministic_work(1);
                if let Some(aliases) = self.pointer_offset_aliases.get(&scaled) {
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
        let mut keys = BTreeSet::from([key.clone()]);
        match &key {
            ConditionMatchKey::Equal(left, right) => {
                let right_spellings = spellings(right);
                for left in spellings(left) {
                    for right in &right_spellings {
                        keys.insert(if left <= *right {
                            ConditionMatchKey::Equal(left.clone(), right.clone())
                        } else {
                            ConditionMatchKey::Equal(right.clone(), left.clone())
                        });
                    }
                }
            }
            ConditionMatchKey::Order(strict, lower, upper) => {
                let upper_spellings = spellings(upper);
                for lower in spellings(lower) {
                    for upper in &upper_spellings {
                        keys.insert(ConditionMatchKey::Order(
                            *strict,
                            lower.clone(),
                            upper.clone(),
                        ));
                    }
                }
            }
            ConditionMatchKey::OffsetEqual(_, _) | ConditionMatchKey::OverflowAdd(_, _) => {
                return None;
            }
        }
        let matches = |facts: &crate::persistent::PersistentMap<ConditionTerm, bool>| {
            facts.iter().any(|(fact, fact_value)| {
                crate::instrumentation::record_deterministic_work(1);
                *fact_value == value && self.condition_matches_for_simp(fact, condition)
            })
        };
        Some(
            keys.iter()
                .any(|key| self.condition_facts_by_sides.get(key).is_some_and(matches))
                || self
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
        self.condition_facts.iter().any(|(fact, value)| {
            let (ConditionTerm::Bitvector32Equal(fact_left, fact_right), true) = (fact, value)
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
        match (fact, target) {
            (
                ConditionTerm::Bitvector32Equal(fact_left, fact_right),
                ConditionTerm::Bitvector32Equal(target_left, target_right),
            ) => {
                bitvector_terms_proven_equal_for_memory_resolution(fact_left, target_left, self)
                    && bitvector_terms_proven_equal_for_memory_resolution(
                        fact_right,
                        target_right,
                        self,
                    )
                    || bitvector_terms_proven_equal_for_memory_resolution(
                        fact_left,
                        target_right,
                        self,
                    ) && bitvector_terms_proven_equal_for_memory_resolution(
                        fact_right,
                        target_left,
                        self,
                    )
            }
            (
                ConditionTerm::PointerOffsetEqual(fact_left, fact_right),
                ConditionTerm::PointerOffsetEqual(target_left, target_right),
            ) => {
                pointer_offsets_proven_equal_for_memory_resolution(fact_left, target_left, self)
                    && pointer_offsets_proven_equal_for_memory_resolution(
                        fact_right,
                        target_right,
                        self,
                    )
                    || pointer_offsets_proven_equal_for_memory_resolution(
                        fact_left,
                        target_right,
                        self,
                    ) && pointer_offsets_proven_equal_for_memory_resolution(
                        fact_right,
                        target_left,
                        self,
                    )
            }
            (
                ConditionTerm::Bitvector32SignedLessThan(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedLessThan(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedLessEqual(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedLessEqual(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedGreaterThan(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedGreaterThan(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedGreaterEqual(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedGreaterEqual(target_left, target_right),
            ) => {
                bitvector_terms_proven_equal_for_memory_resolution(fact_left, target_left, self)
                    && bitvector_terms_proven_equal_for_memory_resolution(
                        fact_right,
                        target_right,
                        self,
                    )
            }
            (
                ConditionTerm::Bitvector32SignedLessThan(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedGreaterThan(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedGreaterThan(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedLessThan(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedLessEqual(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedGreaterEqual(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedGreaterEqual(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedLessEqual(target_left, target_right),
            ) => {
                bitvector_terms_proven_equal_for_memory_resolution(fact_left, target_right, self)
                    && bitvector_terms_proven_equal_for_memory_resolution(
                        fact_right,
                        target_left,
                        self,
                    )
            }
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
            && self.condition_facts.iter().any(|(condition, value)| {
                matches!(
                    (condition, value),
                    (
                        ConditionTerm::Bitvector32SignedLessThan(left, _),
                        true
                    ) if self.bitvector_terms_equal_for_simp(left, base)
                ) || matches!(
                    (condition, value),
                    (
                        ConditionTerm::Bitvector32SignedGreaterThan(_, right),
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

        self.condition_facts.iter().any(|(condition, value)| {
            let (ConditionTerm::Bitvector32Equal(fact_left, fact_right), true) = (condition, value)
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
