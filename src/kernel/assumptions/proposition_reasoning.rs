use super::*;
use crate::kernel::{CompareRelation, OverflowOperation};

/// Discharge one guard left open by a universal instantiation, naming the
/// premises it consumed, or `None` when the retained exact routes do not
/// settle it.
///
/// This is the single rule both sides of the `ForallInt32Instantiation`
/// evidence use: the selector calls it against the full context to build the
/// premise list, and `checks_atomic_derivation` calls it against a context
/// holding exactly that list. It adds no theory: a guard is discharged when
/// it is builtin solvable or exactly available, and the premise it names is
/// the guard itself.
///
/// Narrowing recorded with package 15: the guard used to be discharged by
/// the general prover, whose derivation supplied the premises. An
/// evidence-checked `decide` would restore that, because a guard the frozen
/// condition checker settles could then name what the checker consumed;
/// `decide` does not report its premises today, so a guard that needs one
/// refuses the instantiation rather than being retained with no premise at
/// all, which would make the check vacuous.
fn discharge_instantiation_guard(
    context: &PureFactContext,
    guard: &Proposition,
) -> Option<Vec<Proposition>> {
    if solve_builtin_prop(guard) {
        return Some(Vec::new());
    }
    if context.proves_exact(guard) {
        return Some(vec![guard.clone()]);
    }
    // Anything else would have to name the premises the frozen condition
    // checker consumed, and `decide` does not report them. Refusing the
    // instantiation is the sound alternative: the enclosing search still
    // reaches the goal by another rule when one applies.
    None
}

pub(crate) fn forall_loadable_range_parts(
    proposition: &Proposition,
) -> Option<(Vec<Proposition>, &Proposition)> {
    let Proposition::ForAll {
        sort: Sort::CInt32,
        body,
        ..
    } = proposition
    else {
        return None;
    };
    let mut premises = Vec::new();
    let mut conclusion = body.as_ref();
    while let Proposition::Implies(premise, rest) = conclusion {
        collect_proposition_conjuncts(premise, &mut premises);
        conclusion = rest.as_ref();
    }
    matches!(conclusion, Proposition::CMemoryLoadable { .. }).then_some((premises, conclusion))
}

fn exact_predecessor_base(term: &Bitvector32Term) -> Option<Bitvector32Term> {
    let Bitvector32Term::Subtract(value, amount) = term else {
        return None;
    };
    (amount.as_ref() == &Bitvector32Term::Constant(1)).then(|| value.as_ref().clone())
}

fn exact_predecessor_equal_zero_base(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> Option<Bitvector32Term> {
    if right == &Bitvector32Term::Constant(0) {
        exact_predecessor_base(left)
    } else if left == &Bitvector32Term::Constant(0) {
        exact_predecessor_base(right)
    } else {
        None
    }
}

pub(super) fn canonical_contradiction_condition(condition: &ConditionTerm) -> ConditionTerm {
    fn ordered<T: Ord + Clone>(left: &T, right: &T) -> (T, T) {
        if left <= right {
            (left.clone(), right.clone())
        } else {
            (right.clone(), left.clone())
        }
    }

    match condition {
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left,
            right,
        } => {
            let (left, right) = ordered(left.as_ref(), right.as_ref());
            ConditionTerm::equal(left, right)
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            let (left, right) = ordered(left.as_ref(), right.as_ref());
            ConditionTerm::pointer_offset_equal(left, right)
        }
        ConditionTerm::PointerEqual(left, right) => {
            let (left, right) = ordered(left.as_ref(), right.as_ref());
            ConditionTerm::pointer_equal(left, right)
        }
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterThan,
            left,
            right,
        } => ConditionTerm::signed_less_than(right.as_ref().clone(), left.as_ref().clone()),
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterEqual,
            left,
            right,
        } => ConditionTerm::signed_less_equal(right.as_ref().clone(), left.as_ref().clone()),
        _ => condition.clone(),
    }
}

/// Lazily instantiate a constant-bounded universal. Each requested instance
/// costs one unit plus substitution work; a missing proof stops the caller
/// without lowering the rest of the numeric domain. Two-index smart proofs
/// request nearest pairs first so wider spans can cite their neighbours.
pub(crate) fn finite_forall_goal_instances(
    proposition: &Proposition,
    nearest_pairs: bool,
) -> Option<impl Iterator<Item = (Vec<i64>, Proposition)> + '_> {
    let mut variables = Vec::new();
    let body = collect_forall_chain(proposition, &mut variables);
    if variables.is_empty() {
        return None;
    }
    let ranges =
        crate::kernel::reasoning::finite_forall_ranges_allowing_empty(&variables, body, true)?;
    let empty = ranges.iter().any(|range| range.lower > range.upper);
    let values: Box<dyn Iterator<Item = Vec<i64>>> = if nearest_pairs && ranges.len() == 2 && !empty
    {
        let (a, b) = (i128::from(ranges[0].lower), i128::from(ranges[0].upper));
        let (c, d) = (i128::from(ranges[1].lower), i128::from(ranges[1].upper));
        let minimum = 0.max(a - d).max(c - b);
        let maximum = (a - d).abs().max((b - c).abs());
        Box::new((minimum..=maximum).flat_map(move |span| {
            // Each orientation contributes one interval of first indices.
            // Merge their union to visit (distance, first, second) in order
            // without walking the gap between disjoint intervals.
            let mut intervals = [
                (a.max(c - span), b.min(d - span)),
                (a.max(c + span), b.min(d + span)),
            ];
            intervals.sort_unstable();
            let [(mut low, mut high), (mut next_low, mut next_high)] = intervals;
            if low > high {
                (low, high) = (next_low, next_high);
                (next_low, next_high) = (1, 0);
            } else if next_low <= next_high && next_low <= high + 1 {
                high = high.max(next_high);
                (next_low, next_high) = (1, 0);
            }
            (low..=high)
                .chain(next_low..=next_high)
                .flat_map(move |first| {
                    [first - span, first + span]
                        .into_iter()
                        .enumerate()
                        .filter(move |(orientation, second)| {
                            c <= *second && *second <= d && (span != 0 || *orientation == 0)
                        })
                        .map(move |(_, second)| vec![first as i64, second as i64])
                })
        }))
    } else {
        let mut current =
            (!empty).then(|| ranges.iter().map(|range| range.lower).collect::<Vec<_>>());
        let bounds = ranges.clone();
        Box::new(std::iter::from_fn(move || {
            let result = current.as_ref()?.clone();
            let values = current.as_mut().expect("a live cursor");
            let mut advanced = false;
            for index in (0..values.len()).rev() {
                if values[index] < bounds[index].upper {
                    values[index] += 1;
                    advanced = true;
                    break;
                }
                values[index] = bounds[index].lower;
            }
            if !advanced {
                current = None;
            }
            Some(result)
        }))
    };
    Some(values.map(move |values| {
        crate::instrumentation::record_deterministic_work(1);
        let mut instantiated = body.clone();
        for ((variable, value), range) in variables.iter().zip(&values).zip(&ranges) {
            instantiated = substitute_bitvector_variable_in_proposition(
                &instantiated,
                *variable,
                &range.constant(*value),
            );
        }
        (values, instantiated)
    }))
}

impl PureFactContext {
    /// Narrow a produced equality's selection to its recorded sources,
    /// without proving it again. The evidence remains valid by construction:
    /// the supported rule families name every context fact their check uses.
    pub(crate) fn retained_atomic_equality_context(
        &self,
        evidence: &AtomicPropositionDerivationEvidence,
    ) -> Option<(Self, u64)> {
        let premises = evidence.equality_premises()?;
        if premises.len() >= self.condition_facts.len() + self.prop_facts.len() {
            return None;
        }
        let _timing = crate::instrumentation::OperationTiming::new(
            "kernel",
            "atomic evidence",
            "retained equality premises",
        );
        let mut conditions = Vec::new();
        let mut propositions = Vec::new();
        for premise in premises {
            match premise {
                Proposition::ConditionIs(condition, value) => conditions.push((condition, value)),
                other => propositions.push(other),
            }
        }
        let restricted = self.restricted_to_facts(&conditions, &propositions);
        let id = PureFactContextIdScope::enter(&restricted).id;
        Some((restricted, id))
    }

    /// Decide one *bare* atomic memory or resource proposition with the
    /// retained theory checkers named in `docs/internals/proof-objects.md`.
    ///
    /// This is the obligation-suppression route that survives the removal of
    /// the general prover from lowering and execution. It traverses no
    /// logical structure, chooses no arm, instantiates no quantifier, and
    /// answers `false` for every proposition that is not already one of the
    /// atomic memory or resource shapes. Each arm is exactly the arm
    /// [`Self::proves_atomic_without_search`] uses for that shape, so it can
    /// only lose answers.
    pub(in crate::kernel) fn proves_atomic_memory_or_resource(
        &self,
        proposition: &Proposition,
    ) -> bool {
        match proposition {
            Proposition::CMemoryReadDefined {
                memory,
                pointer,
                value_type,
            } => self.proves_memory_read_defined(memory, pointer, *value_type),
            Proposition::CMemoryLoadable {
                memory,
                base,
                bytes,
                wide: true,
            } => self.proves_native_memory_loadable(memory, base, bytes),
            Proposition::CMemoryLoadable {
                memory,
                base,
                bytes,
                wide: false,
            } => self.proves_memory_loadable(memory, base, bytes),
            Proposition::CMemoryCanStore {
                memory,
                pointer,
                byte_width,
            } => self.proves_memory_access(memory, pointer, *byte_width),
            Proposition::CResourceSeparate { left, right } => {
                self.proves_resource_separate(left, right)
            }
            Proposition::CResourceContains { parent, child } => {
                self.proves_resource_contains(parent, child)
            }
            _ => false,
        }
    }

    // These are stack-budget boundaries, not alternative search strategies.
    // Keep rule-local by-value temporaries out of the recursive dispatcher.

    /// Whether this context settles `proposition` by an exact route: the
    /// fact index, read up to the names of bound variables for a quantified
    /// or conditional proposition, or the frozen checker for one atomic
    /// shape. It searches no logical structure and instantiates nothing, so
    /// a proposition it does not settle is left for a tactic to prove.
    pub(crate) fn settles_exactly(&self, proposition: &Proposition) -> bool {
        self.proves_exact(proposition)
            || match proposition {
                Proposition::ForAll { .. }
                | Proposition::Exists { .. }
                | Proposition::Implies(..) => self.states_required_goal(proposition),
                _ => self.proves_atomic_without_search(proposition),
            }
    }

    pub(crate) fn proves_atomic_without_search(&self, proposition: &Proposition) -> bool {
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                self.decide(condition) == Some(*value)
                    // The memory DAG answers first where it can.
                    || *value
                        && matches!(
                            condition,
                            ConditionTerm::Compare { format: MachineIntegerType::Int32, relation: CompareRelation::Equal, left, right }
                                if crate::kernel::api::atomic_loads_equal_along_memory_derivations(
                                    left, right, self,
                                )
                        )
                    // Two terms for one value that differ only
                    // representationally (memory snapshots embedded in loads,
                    // including under folds and conditionals) are equal by
                    // deep canonicalization; both calls use complete,
                    // input-linear worklists.
                    //
                    // Canonicalization drops what it can prove irrelevant to
                    // the load, which makes it exactly the kind of structural
                    // route that cannot see a store the snapshots no longer
                    // record. It answers to the recorded history like the
                    // others; see `load_equality_refuted_by_history`.
                    || *value
                        && matches!(
                            condition,
                            ConditionTerm::Compare { format: MachineIntegerType::Int32, relation: CompareRelation::Equal, left, right }
                                if crate::kernel::api::canonicalize_atomic_loads(left)
                                        == crate::kernel::api::canonicalize_atomic_loads(right)
                                    && !crate::kernel::reasoning::load_equality_refuted_by_history(
                                        left, right, self,
                                    )
                        )
                    || self.proves_condition_from_facts(condition, *value)
            }
            Proposition::Not(body) => match body.as_ref() {
                Proposition::ConditionIs(condition, value) => {
                    self.decide(condition) == Some(!*value)
                }
                _ => {
                    self.algebraic_constructor_no_confusion_source(proposition)
                        .is_some()
                        || self.prop_facts.contains(proposition)
                }
            },
            Proposition::CMemoryReadDefined {
                memory,
                pointer,
                value_type,
            } => self.proves_memory_read_defined(memory, pointer, *value_type),
            Proposition::CMemoryLoadable {
                memory,
                base,
                bytes,
                wide: true,
            } => self.proves_native_memory_loadable(memory, base, bytes),
            Proposition::CMemoryLoadable {
                memory,
                base,
                bytes,
                wide: false,
            } => {
                self.proves_memory_loadable(memory, base, bytes)
                    // Loadability survives writes: an assumed loadable fact
                    // for the same range transports across any chain of
                    // recorded effects connecting the snapshots. Its
                    // candidates are the loadable facts filed under the
                    // base's block, not every proposition fact.
                    || self.memory_loadable_candidates_for_base(base).any(|fact| {
                        #[cfg(test)]
                        crate::kernel::memory_provenance::CARRIED_LOADABLE_VISITS
                            .with(|visits| visits.set(visits.get() + 1));
                        let Proposition::CMemoryLoadable {
                            memory: fact_memory,
                            base: fact_base,
                            bytes: fact_bytes,
                            wide: false,
                        } = fact
                        else {
                            return false;
                        };
                        {
                            let base_match =
                                crate::kernel::api::canonicalize_pointer_loads(fact_base)
                                    == crate::kernel::api::canonicalize_pointer_loads(base)
                                    || crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
                                        fact_base, base, self,
                                    );
                            let bytes_match = crate::kernel::api::canonicalize_atomic_loads(fact_bytes)
                                == crate::kernel::api::canonicalize_atomic_loads(bytes)
                                || crate::kernel::reasoning::bitvector_terms_proven_equal_for_memory_resolution(
                                    fact_bytes, bytes, self,
                                );
                            base_match
                                && bytes_match
                                && crate::kernel::api::c_memories_connected_by_effects(
                                    fact_memory,
                                    memory,
                                    self,
                                )
                        }
                    })
                    // A goal subrange of a wider assumed loadable span is
                    // loadable when the bounds arithmetic certifies coverage.
                    || crate::kernel::api::loadable_covered_by_fact(self, proposition)
                    // Symbolic byte counts often fold to a constant width,
                    // unlocking the element-index coverage rules.
                    || {
                        let simplified = self.simplify_bitvector_under_assumptions(bytes);
                        simplified != *bytes
                            && self.proves_memory_loadable(memory, base, &simplified)
                    }
            }
            Proposition::CMemoryCanStore {
                memory,
                pointer,
                byte_width,
            } => self.proves_memory_access(memory, pointer, *byte_width),
            Proposition::CResourceSeparate { left, right } => {
                (self.prop_facts.contains(proposition)
                    && !self.resource_separation_conflicts_with_equalities(left, right))
                    || self.proves_resource_separate(left, right)
            }
            Proposition::CResourceContains { parent, child } => {
                self.prop_facts.contains(proposition)
                    || self.proves_resource_contains(parent, child)
            }
            Proposition::And(_, _) | Proposition::Or(_, _) | Proposition::Implies(_, _) => false,
            Proposition::ForAll {
                var, sort, body, ..
            } => {
                self.prop_facts.contains(proposition)
                    || self.quantified_fact_propositions().any(|fact| {
                        let Proposition::ForAll {
                            var: fact_var,
                            sort: fact_sort,
                            body: fact_body,
                            ..
                        } = fact
                        else {
                            return false;
                        };
                        if fact_sort != sort {
                            return false;
                        }
                        let Some(renamed) =
                            crate::kernel::api::substitute_quantified_body_capture_free(
                                fact_body, *fact_var, *var, sort,
                            )
                        else {
                            return false;
                        };
                        renamed == **body
                            || crate::kernel::api::propositions_alpha_equivalent_under_binders(
                                sort, *fact_var, fact_body, *var, body,
                            )
                            || self.propositions_equal_modulo_proven_terms(&renamed, body)
                    })
            }
            Proposition::Exists {
                var, sort, body, ..
            } => {
                self.prop_facts.contains(proposition)
                    || self.proves_exists_from_facts(*var, sort, body)
            }
            _ => self.prop_facts.contains(proposition),
        }
    }

    /// Find an exact variable-to-constructor equality that proves a
    /// constructor disequality. The lookup is indexed by the variable named
    /// by the goal, so a call postcondition such as `link.link == Linked(kid)`
    /// can discharge the next call's `link.link != Empty` prerequisite
    /// without scanning unrelated facts.
    fn algebraic_constructor_no_confusion_source(
        &self,
        proposition: &Proposition,
    ) -> Option<Proposition> {
        let Proposition::Not(body) = proposition else {
            return None;
        };
        let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) = body.as_ref()
        else {
            return None;
        };
        if left.algebraic_type != right.algebraic_type
            || !left.is_well_formed()
            || !right.is_well_formed()
        {
            return None;
        }
        let (variable, forbidden_variant) = match (&left.node, &right.node) {
            (
                AlgebraicTermNode::Variable(variable),
                AlgebraicTermNode::Constructor { variant, .. },
            ) => (*variable, variant),
            (
                AlgebraicTermNode::Constructor { variant, .. },
                AlgebraicTermNode::Variable(variable),
            ) => (*variable, variant),
            _ => return None,
        };
        self.algebraic_variable_constructors
            .get(&variable)?
            .iter()
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
            .find_map(|(source, known_constructor)| {
                if known_constructor.algebraic_type != left.algebraic_type {
                    return None;
                }
                let AlgebraicTermNode::Constructor {
                    variant: known_variant,
                    ..
                } = &known_constructor.node
                else {
                    return None;
                };
                (known_variant != forbidden_variant).then(|| source.clone())
            })
    }

    /// Proves an existential goal without search: an assumed existential over
    /// the same sort proves it up to bound-variable renaming, and an equality
    /// conjunct pinning the bound variable supplies a one-point witness whose
    /// instantiated conjuncts must each prove atomically.
    /// Whether an existential is already witnessed by an exact fact of this
    /// context.
    ///
    /// This is a leaf of [`Self::proves_atomic_without_search`]: it reads the
    /// proposition index, matches a witness structurally, and checks the
    /// instantiated body with the atomic checker. It constructs no
    /// derivation and never re-enters a logical search.
    fn proves_exists_from_facts(&self, var: Variable, sort: &Sort, body: &Proposition) -> bool {
        fn conjuncts_of(proposition: &Proposition, into: &mut Vec<Proposition>) {
            match proposition {
                Proposition::And(left, right) => {
                    conjuncts_of(left, into);
                    conjuncts_of(right, into);
                }
                other => into.push(other.clone()),
            }
        }
        let alpha = self.prop_facts.iter().any(|fact| {
            let Proposition::Exists {
                var: fact_var,
                sort: fact_sort,
                body: fact_body,
                ..
            } = fact
            else {
                return false;
            };
            // The goal may not mention the fact's binder free: renaming the
            // fact's body cannot reach an occurrence the goal leaves free,
            // and a witness for the fact says nothing about that variable.
            fact_sort == sort
                && (*fact_var == var
                    || !crate::kernel::api::proposition_variables(body).contains(fact_var))
                && crate::kernel::api::substitute_quantified_body_capture_free(
                    fact_body, *fact_var, var, sort,
                )
                .is_some_and(|renamed| {
                    crate::kernel::api::propositions_alpha_equivalent(&renamed, body)
                })
        });
        if alpha {
            return true;
        }
        if !matches!(
            sort,
            Sort::CInt32 | Sort::CInt64 | Sort::CMachineInteger(_) | Sort::Bitvector32
        ) {
            return false;
        }
        let mut conjuncts = Vec::new();
        conjuncts_of(body, &mut conjuncts);
        let bound = Bitvector32Term::Variable(var);
        let mut witnesses = Vec::new();
        for conjunct in &conjuncts {
            let (left, right) = match (sort, conjunct) {
                (
                    Sort::CInt64 | Sort::CMachineInteger(MachineIntegerType::UInt64),
                    Proposition::ConditionIs(
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int64,
                            relation: CompareRelation::Equal,
                            left,
                            right,
                        },
                        true,
                    ),
                ) => (left, right),
                (
                    Sort::CInt32
                    | Sort::Bitvector32
                    | Sort::CMachineInteger(
                        MachineIntegerType::Int8
                        | MachineIntegerType::Int16
                        | MachineIntegerType::UInt8
                        | MachineIntegerType::UInt16
                        | MachineIntegerType::UInt32,
                    ),
                    Proposition::ConditionIs(
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int32,
                            relation: CompareRelation::Equal,
                            left,
                            right,
                        },
                        true,
                    ),
                ) => (left, right),
                _ => continue,
            };
            for (side, other) in [(left, right), (right, left)] {
                let mentions_var =
                    substitute_bitvector_variable(other, var, &Bitvector32Term::Constant(0))
                        != **other;
                if **side == bound && !mentions_var {
                    witnesses.push((**other).clone());
                }
            }
        }
        witnesses.iter().any(|witness| {
            conjuncts.iter().all(|conjunct| {
                let instantiated =
                    substitute_bitvector_variable_in_proposition(conjunct, var, witness);
                self.proves_atomic_without_search(&instantiated)
            })
        })
    }

    /// Select one concrete specialization of an available int32 universal,
    /// retaining the exact context facts used to discharge its guards. This
    /// is planning work: check consumes only the recorded fact, argument,
    /// and guard premises and never scans the ambient proposition set.
    /// Select the universal fact and concrete argument that instantiate to
    /// `proposition`, with the guards that instantiation leaves open.
    ///
    /// This is a leaf of the atomic evidence builder, and it is exact: the
    /// candidate arguments come from the goal condition through
    /// `guided_forall_condition_candidates`, and each instantiation guard
    /// must be a builtin-solvable proposition or already discharged by the
    /// retained exact routes. A guard that would need a derivation refuses
    /// the instantiation rather than launching one, and the evidence names
    /// each surviving guard as its own premise.
    pub(crate) fn select_forall_int32_instantiation_evidence(
        &self,
        proposition: &Proposition,
    ) -> Option<ForallInt32InstantiationEvidence> {
        fn conjuncts(proposition: &Proposition, into: &mut Vec<Proposition>) {
            if let Proposition::And(left, right) = proposition {
                conjuncts(left, into);
                conjuncts(right, into);
            } else {
                into.push(proposition.clone());
            }
        }

        let target_condition = match proposition {
            Proposition::ConditionIs(condition, value) => Some((condition, *value)),
            _ => None,
        };
        // Only the universal facts can instantiate: read their set, charged
        // one unit each, not every proposition fact.
        for quantified in self.atomic_quantified_facts.iter() {
            crate::instrumentation::record_deterministic_work(1);
            let quantified = quantified.as_ref();
            let Proposition::ForAll {
                var,
                sort: Sort::CInt32,
                body,
                ..
            } = quantified
            else {
                continue;
            };
            let candidates = match target_condition {
                Some((condition, _)) => {
                    Self::guided_forall_condition_candidates(*var, body, condition)
                }
                None => BTreeSet::new(),
            };
            for argument in candidates {
                let mut conclusion =
                    substitute_bitvector_variable_in_proposition(body, *var, &argument);
                let mut guards = Vec::new();
                while let Proposition::Implies(guard, body) = conclusion {
                    conjuncts(&guard, &mut guards);
                    conclusion = *body;
                }
                let conclusion_matches = conclusion == *proposition
                    || target_condition.is_some_and(|(condition, value)| {
                        self.proposition_proves_condition(&conclusion, condition, value)
                    });
                if !conclusion_matches {
                    continue;
                }
                let mut guard_premises = BTreeSet::new();
                let mut all_guards_proved = true;
                for guard in guards {
                    let Some(premises) = discharge_instantiation_guard(self, &guard) else {
                        all_guards_proved = false;
                        break;
                    };
                    guard_premises.extend(premises);
                }
                if all_guards_proved {
                    return Some(ForallInt32InstantiationEvidence {
                        quantified: quantified.clone(),
                        argument,
                        guard_premises: guard_premises.into_iter().collect(),
                    });
                }
            }
        }
        None
    }

    /// Structural proposition equality where differing bitvector subterms
    /// are accepted when this context proves them equal; an assumed
    /// universal over a loop counter then matches the goal written with the
    /// counter's proven final value.
    fn propositions_equal_modulo_proven_terms(
        &self,
        left: &Proposition,
        right: &Proposition,
    ) -> bool {
        if left == right {
            return true;
        }
        match (left, right) {
            (Proposition::And(al, ar), Proposition::And(bl, br))
            | (Proposition::Or(al, ar), Proposition::Or(bl, br))
            | (Proposition::Implies(al, ar), Proposition::Implies(bl, br)) => {
                self.propositions_equal_modulo_proven_terms(al, bl)
                    && self.propositions_equal_modulo_proven_terms(ar, br)
            }
            (Proposition::Not(a), Proposition::Not(b)) => {
                self.propositions_equal_modulo_proven_terms(a, b)
            }
            (
                Proposition::ConditionIs(left_condition, left_value),
                Proposition::ConditionIs(right_condition, right_value),
            ) if left_value == right_value => {
                self.conditions_equal_modulo_proven_terms(left_condition, right_condition)
            }
            _ => false,
        }
    }

    fn conditions_equal_modulo_proven_terms(
        &self,
        left: &ConditionTerm,
        right: &ConditionTerm,
    ) -> bool {
        if left == right {
            return true;
        }
        let operands = match (left, right) {
            (
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: a,
                    right: b,
                },
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: c,
                    right: d,
                },
            )
            | (
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: a,
                    right: b,
                },
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: c,
                    right: d,
                },
            )
            | (
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterThan,
                    left: a,
                    right: b,
                },
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterThan,
                    left: c,
                    right: d,
                },
            )
            | (
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterEqual,
                    left: a,
                    right: b,
                },
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterEqual,
                    left: c,
                    right: d,
                },
            )
            | (
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: a,
                    right: b,
                },
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: c,
                    right: d,
                },
            ) => Some((a, b, c, d)),
            _ => None,
        };
        let Some((a, b, c, d)) = operands else {
            return false;
        };
        let le_holds = |x: &Bitvector32Term, y: &Bitvector32Term| {
            let condition = ConditionTerm::signed_less_equal(x.clone(), y.clone());
            self.decide(&condition) == Some(true)
                || self.proves_condition_from_facts(&condition, true)
        };
        let terms_equal = |x: &Bitvector32Term, y: &Bitvector32Term| {
            x == y
                || self.decide(&ConditionTerm::equal(x.clone(), y.clone())) == Some(true)
                || self.proves_condition_from_facts(
                    &ConditionTerm::equal(x.clone(), y.clone()),
                    true,
                )
                // Antisymmetry: mutual non-strict bounds prove equality.
                || (le_holds(x, y) && le_holds(y, x))
        };
        terms_equal(a, c) && terms_equal(b, d)
    }

    /// Whether the atomic theory checkers settle `proposition` against this
    /// exact premise set.
    ///
    /// This is the boolean form of the retained atomic route: it runs the
    /// same arms the evidence builder does but retains nothing, so a kernel
    /// caller that only needs a verdict never constructs a derivation.
    pub(in crate::kernel) fn proves_atomic_for_derivation(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> bool {
        self.proves_atomic_for_derivation_with_id(proposition, for_simp)
            .0
            .is_some()
    }

    pub(crate) fn proves_atomic_for_derivation_with_id(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> (Option<AtomicPropositionDerivationEvidence>, u64) {
        let id_scope = PureFactContextIdScope::enter(self);
        let premises_id = id_scope.id;
        if let Some(result) = ATOMIC_DERIVATION_MEMO.with(|memo| {
            memo.borrow()
                .get(&atomic_derivation_memo_key(premises_id, for_simp))
                .and_then(|entries| entries.get(proposition))
                .cloned()
        }) {
            return (result, premises_id);
        }
        if let Proposition::ConditionIs(condition, value) = proposition
            && self.decide_widened_sum_bound(condition) == Some(*value)
        {
            return (
                Some(AtomicPropositionDerivationEvidence::WidenedUnsignedSumBound),
                premises_id,
            );
        }
        let epoch_before = INCOMPLETE_REASONING_EPOCH.with(Cell::get);
        let memory_evidence = match proposition {
            // Both equality widths reach the history. An `int64` load is a
            // `Bitvector32Term::MemoryLoad` under a 64-bit equality, and the
            // walk that decides whether two of them read one version of a
            // cell takes its byte width from the load registry, so it has
            // always been the same question. Only this arm was narrower than
            // the question, which left a 64-bit load equality neither proved
            // nor refuted by the recorded history.
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                }
                | ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                true,
            ) => crate::kernel::api::atomic_memory_load_equality_evidence(left, right, self)
                .filter(AtomicMemoryLoadEqualityEvidence::is_fully_typed)
                .map(Box::new)
                .map(AtomicPropositionDerivationEvidence::MemoryDag),
            Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(left, right), true) => {
                crate::kernel::api::pointer_offset_equality_evidence(left, right, self)
                    .map(Box::new)
                    .map(AtomicPropositionDerivationEvidence::PointerOffsetMemoryDag)
            }
            _ => None,
        };
        let load_address_congruence_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                true,
            ) => self
                .load_address_congruence_evidence(left, right)
                .map(Box::new)
                .map(AtomicPropositionDerivationEvidence::LoadAddressCongruence),
            _ => None,
        };
        let signed_order_evidence = match proposition {
            Proposition::ConditionIs(condition, value) => {
                condition_as_order_fact(condition, *value)
                    .and_then(|(left, right, strict)| {
                        self.exact_signed_order_path_evidence(&left, &right, strict)
                    })
                    .map(AtomicPropositionDerivationEvidence::SignedOrderPath)
            }
            _ => None,
        };
        let wide_order_evidence = match proposition {
            Proposition::ConditionIs(condition, value) => {
                [true, false].into_iter().find_map(|unsigned| {
                    let (left, right, strict) =
                        super::condition_reasoning::wide_order_fact(condition, *value, unsigned)?;
                    self.exact_wide_order_path_evidence(&left, &right, strict, unsigned)
                        .map(|path| AtomicPropositionDerivationEvidence::WideOrderPath {
                            unsigned,
                            path,
                        })
                })
            }
            _ => None,
        };
        let equality_path_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                true,
            ) => self
                .exact_bitvector_equality_path_evidence(left, right)
                .map(AtomicPropositionDerivationEvidence::BitvectorEqualityPath),
            _ => None,
        };
        let pinned_constant_equality_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                true,
            ) if self
                .equality_graph
                .exact_literal_sources(left.as_ref())
                .is_some()
                || self
                    .equality_graph
                    .exact_literal_sources(right.as_ref())
                    .is_some() =>
            {
                self.direct_bitvector_equality_evidence(left, right)
                    .map(Box::new)
                    .map(AtomicPropositionDerivationEvidence::Int32PinnedConstantEquality)
            }
            _ => None,
        };
        let le_and_not_lt_equality_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                true,
            ) => {
                let less_equal =
                    ConditionTerm::signed_less_equal(left.as_ref().clone(), right.as_ref().clone());
                let less_than =
                    ConditionTerm::signed_less_than(left.as_ref().clone(), right.as_ref().clone());
                let less_equal = Proposition::ConditionIs(less_equal, true);
                let not_less_than = Proposition::ConditionIs(less_than, false);
                (self.contains_assumed_exact(&less_equal)
                    && self.contains_assumed_exact(&not_less_than))
                .then(|| {
                    AtomicPropositionDerivationEvidence::Int32LeAndNotLtImpliesEquality(Box::new(
                        Int32LeAndNotLtEqualityEvidence {
                            less_equal,
                            not_less_than,
                        },
                    ))
                })
            }
            _ => None,
        };
        let ge_and_not_gt_equality_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                true,
            ) => {
                let greater_equal = ConditionTerm::signed_greater_equal(
                    left.as_ref().clone(),
                    right.as_ref().clone(),
                );
                let greater_than = ConditionTerm::signed_greater_than(
                    left.as_ref().clone(),
                    right.as_ref().clone(),
                );
                let greater_equal = Proposition::ConditionIs(greater_equal, true);
                let not_greater_than = Proposition::ConditionIs(greater_than, false);
                (self.contains_assumed_exact(&greater_equal)
                    && self.contains_assumed_exact(&not_greater_than))
                .then(|| {
                    AtomicPropositionDerivationEvidence::Int32GeAndNotGtImpliesEquality(Box::new(
                        Int32GeAndNotGtEqualityEvidence {
                            greater_equal,
                            not_greater_than,
                        },
                    ))
                })
            }
            _ => None,
        };
        let le_and_neq_strict_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left,
                    right,
                },
                true,
            ) => {
                let less_equal = Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(left.as_ref().clone(), right.as_ref().clone()),
                    true,
                );
                let not_equal = Proposition::ConditionIs(
                    ConditionTerm::equal(left.as_ref().clone(), right.as_ref().clone()),
                    false,
                );
                (self.contains_assumed_exact(&less_equal)
                    && self.contains_assumed_exact(&not_equal))
                .then(|| {
                    AtomicPropositionDerivationEvidence::Int32LeAndNeqImpliesStrict(Box::new(
                        Int32LeAndNeqStrictEvidence {
                            less_equal,
                            not_equal,
                        },
                    ))
                })
            }
            _ => None,
        };
        let increment_upper_bound_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: incremented,
                    right: upper,
                },
                true,
            ) => incremented
                .add_const_base(1)
                .and_then(|base| self.exact_direct_order_step(&base, upper, true))
                .map(Box::new)
                .map(AtomicPropositionDerivationEvidence::Int32IncrementUpperBound),
            _ => None,
        };
        let increment_constant_upper_bound_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: incremented,
                    right: goal_upper,
                },
                true,
            ) => incremented
                .add_const_base(1)
                .and_then(|base| {
                    let Bitvector32Term::Constant(goal_bits) = goal_upper.as_ref() else {
                        return None;
                    };
                    self.signed_order_bound_entries(&base).find_map(
                        |(fact_endpoint, candidate, strict, forward)| {
                            let Bitvector32Term::Constant(candidate_bits) = &candidate else {
                                return None;
                            };
                            (!strict && forward && (*candidate_bits as i32) < (*goal_bits as i32))
                                .then(|| {
                                    self.exact_direct_order_step(&fact_endpoint, &candidate, false)
                                })
                                .flatten()
                        },
                    )
                })
                .map(Box::new)
                .map(AtomicPropositionDerivationEvidence::Int32IncrementConstantUpperBound),
            _ => None,
        };
        let increment_strictly_increases_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: base,
                    right: incremented,
                },
                true,
                // The goal's base and the increment's base may be different
                // terms for one value (a load and its load variable); the
                // tie is canonical, while the selected premise cites the
                // exact fact.
            ) if incremented
                .add_const_base(1)
                .as_ref()
                .is_some_and(|increment_base| {
                    crate::kernel::eval::terms_have_same_canonical_form(increment_base, base)
                }) =>
            {
                self.exact_direct_strict_upper_bound_step(base)
                    .map(Box::new)
                    .map(AtomicPropositionDerivationEvidence::Int32IncrementStrictlyIncreases)
            }
            _ => None,
        };
        let one_plus_strictly_increases_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: value,
                    right: sum,
                },
                true,
            ) => match sum.as_ref() {
                Bitvector32Term::Add(left, right)
                    if left.as_ref() == &Bitvector32Term::Constant(1)
                        && right.as_ref() == value.as_ref() =>
                {
                    let int_max = Bitvector32Term::Constant(i32::MAX as u32);
                    self.exact_direct_order_step(value, &int_max, true)
                        .map(Box::new)
                        .map(AtomicPropositionDerivationEvidence::Int32OnePlusStrictlyIncreases)
                }
                _ => None,
            },
            _ => None,
        };
        let increment_below_max_is_defined_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Overflows {
                    format: MachineIntegerType::Int32,
                    op: OverflowOperation::Add,
                    left: base,
                    right: amount,
                },
                false,
            ) if amount.as_ref() == &Bitvector32Term::Constant(1) => {
                let int_max = Bitvector32Term::Constant(i32::MAX as u32);
                self.exact_signed_order_path_evidence(base, &int_max, true)
                    .and_then(|path| match path.as_slice() {
                        [step] if step.lower == **base && step.upper == int_max && step.strict => {
                            Some(step.clone())
                        }
                        _ => None,
                    })
                    .map(Box::new)
                    .map(AtomicPropositionDerivationEvidence::Int32IncrementBelowMaxIsDefined)
            }
            _ => None,
        };
        let one_plus_below_max_is_defined_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Overflows {
                    format: MachineIntegerType::Int32,
                    op: OverflowOperation::Add,
                    left: one,
                    right: value,
                },
                false,
            ) if one.as_ref() == &Bitvector32Term::Constant(1) => {
                let int_max = Bitvector32Term::Constant(i32::MAX as u32);
                self.exact_direct_order_step(value, &int_max, true)
                    .map(Box::new)
                    .map(AtomicPropositionDerivationEvidence::Int32OnePlusBelowMaxIsDefined)
            }
            _ => None,
        };
        let nonnegative_add_within_max_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Overflows {
                    format: MachineIntegerType::Int32,
                    op: OverflowOperation::Add,
                    left: value,
                    right: amount,
                },
                false,
            ) => {
                let zero = Bitvector32Term::Constant(0);
                let headroom = Bitvector32Term::Subtract(
                    Box::new(Bitvector32Term::Constant(i32::MAX as u32)),
                    Box::new(amount.as_ref().clone()),
                );
                self.exact_direct_order_step(&zero, amount, false)
                    .zip(self.exact_direct_order_step(value, &headroom, false))
                    .map(|(amount_nonnegative, within_headroom)| {
                        AtomicPropositionDerivationEvidence::Int32NonnegativeAddWithinMaxIsDefined(
                            Box::new(Int32NonnegativeAddWithinMaxEvidence {
                                amount_nonnegative,
                                within_headroom,
                            }),
                        )
                    })
            }
            _ => None,
        };
        let nonnegative_subtract_within_value_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Overflows {
                    format: MachineIntegerType::Int32,
                    op: OverflowOperation::Subtract,
                    left: value,
                    right: amount,
                },
                false,
            ) => {
                let zero = Bitvector32Term::Constant(0);
                self.exact_direct_order_step(&zero, amount, false)
                    .zip(self.exact_direct_order_step(amount, value, false))
                    .map(|(amount_nonnegative, within_value)| {
                        AtomicPropositionDerivationEvidence::Int32NonnegativeSubtractWithinValueIsDefined(
                            Box::new(Int32NonnegativeSubtractWithinValueEvidence {
                                amount_nonnegative,
                                within_value,
                            }),
                        )
                    })
            }
            _ => None,
        };
        let increment_lower_bound_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: lower,
                    right: incremented,
                },
                true,
            ) => incremented.add_const_base(1).and_then(|base| {
                self.exact_increment_bounds_evidence(lower, &base)
                    .map(AtomicPropositionDerivationEvidence::Int32IncrementLowerBound)
            }),
            _ => None,
        };
        let increment_greater_equal_lower_bound_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterEqual,
                    left: incremented,
                    right: lower,
                },
                true,
            ) => incremented.add_const_base(1).and_then(|base| {
                self.exact_increment_bounds_evidence(lower, &base)
                    .map(AtomicPropositionDerivationEvidence::Int32IncrementGreaterEqualLowerBound)
            }),
            _ => None,
        };
        let increment_strict_greater_lower_bound_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterThan,
                    left: incremented,
                    right: lower,
                },
                true,
            ) => incremented.add_const_base(1).and_then(|base| {
                self.exact_increment_bounds_evidence(lower, &base)
                    .map(AtomicPropositionDerivationEvidence::Int32IncrementStrictGreaterLowerBound)
            }),
            _ => None,
        };
        let increment_strict_greater_from_strict_lower_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterThan,
                    left: incremented,
                    right: lower,
                },
                true,
            ) => incremented.add_const_base(1).and_then(|base| {
                self.exact_strict_increment_bounds_evidence(lower, &base).map(|bounds| {
                    AtomicPropositionDerivationEvidence::Int32IncrementStrictGreaterFromStrictLower(
                        bounds,
                    )
                })
            }),
            _ => None,
        };
        let increment_preserves_order_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: incremented_lower,
                    right: incremented_value,
                },
                true,
            ) => incremented_lower
                .add_const_base(1)
                .zip(incremented_value.add_const_base(1))
                .and_then(|(lower, value)| {
                    self.exact_increment_bounds_evidence(&lower, &value)
                        .map(AtomicPropositionDerivationEvidence::Int32IncrementPreservesOrder)
                }),
            _ => None,
        };
        // `0 <= value` and `value >= 0` are one order; the theorem's
        // `0 <= value` conclusion closes either spelling.
        let positive_is_nonnegative_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: lower,
                    right: value,
                }
                | ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterEqual,
                    left: value,
                    right: lower,
                },
                true,
            ) if lower.as_ref() == &Bitvector32Term::Constant(0) => self
                .exact_direct_order_step(&Bitvector32Term::Constant(0), value, true)
                .map(Box::new)
                .map(AtomicPropositionDerivationEvidence::Int32PositiveIsNonnegative),
            _ => None,
        };
        let successor_le_implies_lt_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: lower,
                    right: value,
                },
                true,
            )
            | Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterThan,
                    left: value,
                    right: lower,
                },
                true,
            ) => match lower.as_ref() {
                Bitvector32Term::Constant(lower_bits) => (*lower_bits as i32)
                    .checked_add(1)
                    .and_then(|successor| {
                        self.exact_direct_order_step(
                            &Bitvector32Term::Constant(successor as u32),
                            value,
                            false,
                        )
                    })
                    .map(Box::new)
                    .map(AtomicPropositionDerivationEvidence::Int32SuccessorLeImpliesLt),
                _ => None,
            },
            _ => None,
        };
        let constant_lower_bound_weakening_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: goal_lower,
                    right: value,
                },
                true,
            ) => match goal_lower.as_ref() {
                Bitvector32Term::Constant(goal_bits) => self
                    .signed_order_bound_entries(value.as_ref())
                    .find_map(|(fact_endpoint, candidate, strict, forward)| {
                        let Bitvector32Term::Constant(candidate_bits) = &candidate else {
                            return None;
                        };
                        (!strict && !forward && (*goal_bits as i32) < (*candidate_bits as i32))
                            .then(|| {
                                self.exact_direct_order_step(&candidate, &fact_endpoint, false)
                            })
                            .flatten()
                    })
                    .map(Box::new)
                    .map(AtomicPropositionDerivationEvidence::Int32ConstantLowerBoundWeakening),
                _ => None,
            },
            _ => None,
        };
        let negated_strict_successor_bound_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterEqual,
                    left: value,
                    right: lower,
                },
                true,
            ) => match lower.as_ref() {
                Bitvector32Term::Constant(lower_bits) => {
                    (*lower_bits as i32).checked_add(1).and_then(|upper| {
                        let upper = Bitvector32Term::Constant(upper as u32);
                        let premise = Proposition::ConditionIs(
                            ConditionTerm::signed_less_than(value.as_ref().clone(), upper.clone()),
                            false,
                        );
                        self.contains_assumed_exact(&premise).then(|| {
                            AtomicPropositionDerivationEvidence::Int32NegatedStrictSuccessorBound(
                                Box::new(SignedOrderDerivationStep {
                                    lower: upper,
                                    upper: value.as_ref().clone(),
                                    strict: false,
                                    premise,
                                }),
                            )
                        })
                    })
                }
                _ => None,
            },
            _ => None,
        };
        let positive_predecessor_is_nonnegative_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: lower,
                    right: predecessor,
                },
                true,
            ) if lower.as_ref() == &Bitvector32Term::Constant(0) => {
                exact_predecessor_base(predecessor).and_then(|value| {
                    self.exact_direct_order_step(&Bitvector32Term::Constant(0), &value, true)
                    .map(Box::new)
                    .map(AtomicPropositionDerivationEvidence::Int32PositivePredecessorIsNonnegative)
                })
            }
            _ => None,
        };
        let positive_predecessor_strictly_decreases_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare { format: MachineIntegerType::Int32, relation: CompareRelation::LessThan, left: predecessor, right: value },
                true,
            ) => exact_predecessor_base(predecessor)
                .filter(|base| base == value.as_ref())
                .and_then(|base| {
                    self.exact_direct_order_step(
                        &Bitvector32Term::Constant(0),
                        &base,
                        true,
                    )
                    .map(Box::new).map(AtomicPropositionDerivationEvidence::Int32PositivePredecessorStrictlyDecreases)
                }),
            _ => None,
        };
        let nonnegative_predecessor_upper_bound_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: predecessor,
                    right: upper,
                },
                true,
            ) => exact_predecessor_base(predecessor).and_then(|value| {
                let nonnegative =
                    self.exact_direct_order_step(&Bitvector32Term::Constant(0), &value, false)?;
                let upper_bound = self.exact_direct_order_step(&value, upper, false)?;
                Some(
                    AtomicPropositionDerivationEvidence::Int32NonnegativePredecessorUpperBound(
                        Box::new(Int32PredecessorUpperBoundEvidence {
                            nonnegative,
                            upper_bound,
                        }),
                    ),
                )
            }),
            _ => None,
        };
        let one_le_predecessor_is_nonnegative_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: lower,
                    right: predecessor,
                },
                true,
            ) if lower.as_ref() == &Bitvector32Term::Constant(0) => {
                exact_predecessor_base(predecessor).and_then(|value| {
                    self.exact_one_le_evidence(&value).map(
                        AtomicPropositionDerivationEvidence::Int32OneLePredecessorIsNonnegative,
                    )
                })
            }
            _ => None,
        };
        let one_le_predecessor_strictly_decreases_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: predecessor,
                    right: value,
                },
                true,
            ) => exact_predecessor_base(predecessor)
                .filter(|base| base == value.as_ref())
                .and_then(|base| {
                    self.exact_one_le_evidence(&base).map(
                        AtomicPropositionDerivationEvidence::Int32OneLePredecessorStrictlyDecreases,
                    )
                }),
            _ => None,
        };
        let equal_one_predecessor_is_zero_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                true,
            ) => exact_predecessor_equal_zero_base(left, right).and_then(|value| {
                self.exact_bitvector_equality_path_evidence(&value, &Bitvector32Term::Constant(1))
                    .map(AtomicPropositionDerivationEvidence::Int32EqualOnePredecessorIsZero)
            }),
            _ => None,
        };
        let forall_instantiation_evidence = self
            .select_forall_int32_instantiation_evidence(proposition)
            .map(|evidence| {
                AtomicPropositionDerivationEvidence::ForallInt32Instantiation(Box::new(evidence))
            });
        let pointer_word_evidence = match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                value,
            ) => {
                let mut used = crate::kernel::eval::pointer_tags::UsedFacts::new();
                self.decide_pointer_word_equality_citing(left, right, &mut used)
                    .filter(|decided| decided == value && used.complete)
                    .map(|_| {
                        AtomicPropositionDerivationEvidence::PointerWord(Box::new(
                            PointerWordEvidence {
                                premises: used.premises,
                            },
                        ))
                    })
            }
            _ => None,
        };
        let pointer_alignment_evidence = match proposition {
            Proposition::ConditionIs(condition, value) => condition
                .as_pointer_alignment()
                .and_then(|(pointer, alignment)| {
                    self.pointer_alignment_certificate_decision(pointer, alignment)
                })
                .filter(|(aligned, _)| aligned == value)
                .map(|(_, premise)| {
                    AtomicPropositionDerivationEvidence::PointerAlignment(Box::new(
                        PointerAlignmentEvidence { premise },
                    ))
                }),
            _ => None,
        };
        let algebraic_constructor_no_confusion_evidence = self
            .algebraic_constructor_no_confusion_source(proposition)
            .map(|source| {
                AtomicPropositionDerivationEvidence::AlgebraicConstructorNoConfusion(Box::new(
                    source,
                ))
            });
        let result = memory_evidence
            .or(load_address_congruence_evidence)
            .or(equality_path_evidence)
            .or(le_and_not_lt_equality_evidence)
            .or(ge_and_not_gt_equality_evidence)
            .or(le_and_neq_strict_evidence)
            .or(positive_is_nonnegative_evidence)
            .or(successor_le_implies_lt_evidence)
            .or(constant_lower_bound_weakening_evidence)
            .or(negated_strict_successor_bound_evidence)
            .or(pinned_constant_equality_evidence)
            .or(signed_order_evidence)
            .or(wide_order_evidence)
            .or(increment_upper_bound_evidence)
            .or(increment_constant_upper_bound_evidence)
            .or(one_plus_strictly_increases_evidence)
            .or(increment_strictly_increases_evidence)
            .or(increment_below_max_is_defined_evidence)
            .or(one_plus_below_max_is_defined_evidence)
            .or(nonnegative_add_within_max_evidence)
            .or(nonnegative_subtract_within_value_evidence)
            .or(increment_lower_bound_evidence)
            .or(increment_greater_equal_lower_bound_evidence)
            .or(increment_strict_greater_lower_bound_evidence)
            .or(increment_strict_greater_from_strict_lower_evidence)
            .or(increment_preserves_order_evidence)
            .or(positive_predecessor_is_nonnegative_evidence)
            .or(positive_predecessor_strictly_decreases_evidence)
            .or(nonnegative_predecessor_upper_bound_evidence)
            .or(one_le_predecessor_is_nonnegative_evidence)
            .or(one_le_predecessor_strictly_decreases_evidence)
            .or(equal_one_predecessor_is_zero_evidence)
            .or(forall_instantiation_evidence)
            .or(pointer_alignment_evidence)
            .or(pointer_word_evidence)
            .or(algebraic_constructor_no_confusion_evidence)
            .or_else(|| {
                let proved = if for_simp {
                    match proposition {
                        Proposition::ConditionIs(condition, value) => {
                            self.decide_condition_for_simp(condition) == Some(*value)
                        }
                        Proposition::Not(body) => match body.as_ref() {
                            Proposition::ConditionIs(condition, value) => {
                                self.decide_condition_for_simp(condition) == Some(!*value)
                            }
                            _ => self.prop_facts.contains(proposition),
                        },
                        _ => self.proves_atomic_without_search(proposition),
                    }
                } else {
                    self.proves_atomic_without_search(proposition)
                };
                proved.then_some(AtomicPropositionDerivationEvidence::Legacy)
            });
        if result.is_some() || INCOMPLETE_REASONING_EPOCH.with(Cell::get) == epoch_before {
            ATOMIC_DERIVATION_MEMO.with(|memo| {
                let mut memo = memo.borrow_mut();
                if memo.len() >= ASSUMPTIONS_MEMO_ID_LIMIT {
                    memo.clear();
                }
                let entries = memo
                    .entry(atomic_derivation_memo_key(premises_id, for_simp))
                    .or_default();
                if entries.len() >= DECIDE_MEMO_LIMIT {
                    entries.clear();
                }
                entries.insert(proposition.clone(), result.clone());
            });
        }
        (result, premises_id)
    }

    pub(super) fn checks_atomic_derivation(
        &self,
        proposition: &Proposition,
        for_simp: bool,
        premises_id: u64,
        evidence: &AtomicPropositionDerivationEvidence,
    ) -> bool {
        if let AtomicPropositionDerivationEvidence::PointerWord(evidence) = evidence {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                value,
            ) = proposition
            else {
                return false;
            };
            if evidence
                .premises
                .iter()
                .any(|premise| !self.contains_assumed_exact(premise))
            {
                return false;
            }
            let premises = evidence
                .premises
                .iter()
                .fold(PureFactContext::new(), |context, premise| {
                    context.assume_proposition(premise.clone())
                });
            let mut used = crate::kernel::eval::pointer_tags::UsedFacts::new();
            return premises.decide_pointer_word_equality_citing(left, right, &mut used)
                == Some(*value);
        }
        if let AtomicPropositionDerivationEvidence::PointerAlignment(evidence) = evidence {
            let Proposition::ConditionIs(condition, value) = proposition else {
                return false;
            };
            let Some((pointer, alignment)) = condition.as_pointer_alignment() else {
                return false;
            };
            // Check against exactly the retained base fact (or none for a
            // heap base) so the check never consults a wider context than
            // the certificate names.
            let premises = match &evidence.premise {
                Some(premise) => {
                    if !self.contains_assumed_exact(premise) {
                        return false;
                    }
                    PureFactContext::new().assume_proposition(premise.clone())
                }
                None => PureFactContext::new(),
            };
            return premises.decide_pointer_alignment(pointer, alignment) == Some(*value);
        }
        if let AtomicPropositionDerivationEvidence::AlgebraicConstructorNoConfusion(source) =
            evidence
        {
            return self.contains_assumed_exact(source)
                && self
                    .algebraic_constructor_no_confusion_source(proposition)
                    .is_some_and(|candidate| candidate == **source);
        }
        if let AtomicPropositionDerivationEvidence::MemoryDag(evidence) = evidence {
            return evidence.checks(proposition, self);
        }
        if let AtomicPropositionDerivationEvidence::LoadAddressCongruence(evidence) = evidence {
            return evidence.checks(proposition, self);
        }
        if let AtomicPropositionDerivationEvidence::PointerOffsetMemoryDag(evidence) = evidence {
            let Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(left, right), true) =
                proposition
            else {
                return false;
            };
            return evidence.checks(left, right, self);
        }
        if let AtomicPropositionDerivationEvidence::BitvectorEqualityPath(path) = evidence {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                true,
            ) = proposition
            else {
                return false;
            };
            return self.checks_exact_bitvector_equality_path(path, left, right);
        }
        if let AtomicPropositionDerivationEvidence::ForallInt32Instantiation(selected) = evidence {
            let Proposition::ForAll {
                var,
                sort: Sort::CInt32,
                body,
                ..
            } = &selected.quantified
            else {
                return false;
            };
            if !self.prop_facts.contains(&selected.quantified)
                || selected
                    .guard_premises
                    .iter()
                    .any(|premise| !self.proves_exact(premise))
            {
                return false;
            }
            // Each guard the instantiation leaves open is discharged
            // against exactly the premises the evidence names, by the same
            // exact function the selector used to build it. Construction and
            // verification therefore decide one goal by one rule, and the
            // check never consults a wider context than the evidence cites.
            let guard_context = selected
                .guard_premises
                .iter()
                .fold(PureFactContext::new(), |context, premise| {
                    context.assume_proposition(premise.clone())
                });
            let mut conclusion =
                substitute_bitvector_variable_in_proposition(body, *var, &selected.argument);
            while let Proposition::Implies(guard, body) = conclusion {
                let mut conjuncts = Vec::new();
                collect_proposition_conjuncts(&guard, &mut conjuncts);
                for conjunct in conjuncts {
                    if discharge_instantiation_guard(&guard_context, &conjunct).is_none() {
                        return false;
                    }
                }
                conclusion = *body;
            }
            return conclusion == *proposition
                || match proposition {
                    Proposition::ConditionIs(condition, value) => {
                        self.proposition_proves_condition(&conclusion, condition, *value)
                    }
                    _ => false,
                };
        }
        if let AtomicPropositionDerivationEvidence::SignedOrderPath(path) = evidence {
            let Proposition::ConditionIs(condition, value) = proposition else {
                return false;
            };
            let Some((left, right, require_strict)) = condition_as_order_fact(condition, *value)
            else {
                return false;
            };
            let mut current = &left;
            let mut strict = false;
            for step in path {
                if current != &step.lower
                    || !matches!(
                        &step.premise,
                        Proposition::ConditionIs(condition, value)
                            if self.exact_condition_value(condition) == Some(*value)
                                && condition_as_order_fact(condition, *value)
                                    == Some((step.lower.clone(), step.upper.clone(), step.strict))
                    )
                {
                    return false;
                }
                current = &step.upper;
                strict |= step.strict;
            }
            let constant_connection = signed_bitvector_constant(current)
                .zip(signed_bitvector_constant(&right))
                .and_then(|(current, right)| (current <= right).then_some(current < right));
            return (current == &right || constant_connection.is_some())
                && (!require_strict || strict || constant_connection == Some(true));
        }
        if let AtomicPropositionDerivationEvidence::WideOrderPath { unsigned, path } = evidence {
            let Proposition::ConditionIs(condition, value) = proposition else {
                return false;
            };
            let Some((left, right, require_strict)) =
                super::condition_reasoning::wide_order_fact(condition, *value, *unsigned)
            else {
                return false;
            };
            let canonical = crate::kernel::eval::canonical_term;
            let mut current = canonical(&left);
            let mut strict = false;
            for step in path {
                if current != canonical(&step.lower)
                    || !matches!(
                        &step.premise,
                        Proposition::ConditionIs(condition, value)
                            if self.exact_condition_value(condition) == Some(*value)
                                && super::condition_reasoning::wide_order_fact(
                                    condition, *value, *unsigned,
                                ) == Some((step.lower.clone(), step.upper.clone(), step.strict))
                    )
                {
                    return false;
                }
                current = canonical(&step.upper);
                strict |= step.strict;
            }
            return !path.is_empty() && current == canonical(&right) && (!require_strict || strict);
        }
        if let AtomicPropositionDerivationEvidence::Int32IncrementUpperBound(step) = evidence {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: incremented,
                    right: upper,
                },
                true,
            ) = proposition
            else {
                return false;
            };
            let Some(base) = incremented.add_const_base(1) else {
                return false;
            };
            return step.lower == base
                && step.upper == **upper
                && step.strict
                && matches!(
                    &step.premise,
                    Proposition::ConditionIs(condition, value)
                        if self.exact_condition_value(condition) == Some(*value)
                            && condition_as_order_fact(condition, *value)
                                == Some((step.lower.clone(), step.upper.clone(), true))
                );
        }
        if let AtomicPropositionDerivationEvidence::Int32IncrementConstantUpperBound(step) =
            evidence
        {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: incremented,
                    right: goal_upper,
                },
                true,
            ) = proposition
            else {
                return false;
            };
            let Some(base) = incremented.add_const_base(1) else {
                return false;
            };
            let (Bitvector32Term::Constant(premise_bits), Bitvector32Term::Constant(goal_bits)) =
                (&step.upper, goal_upper.as_ref())
            else {
                return false;
            };
            return step.lower == base
                && (*premise_bits as i32) < (*goal_bits as i32)
                && !step.strict
                && self.checks_exact_order_step(step);
        }
        if let AtomicPropositionDerivationEvidence::Int32IncrementStrictlyIncreases(step) = evidence
        {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: base,
                    right: incremented,
                },
                true,
            ) = proposition
            else {
                return false;
            };
            // The premise cites the exact fact; its tie to the goal's base
            // is canonical, which is deterministic and so checks
            // identically.
            return incremented
                .add_const_base(1)
                .as_ref()
                .is_some_and(|increment_base| {
                    crate::kernel::eval::terms_have_same_canonical_form(increment_base, base)
                })
                && crate::kernel::eval::terms_have_same_canonical_form(&step.lower, base)
                && step.strict
                && matches!(
                    &step.premise,
                    Proposition::ConditionIs(condition, value)
                        if self.exact_condition_value(condition) == Some(*value)
                            && condition_as_order_fact(condition, *value)
                                == Some((step.lower.clone(), step.upper.clone(), true))
                );
        }
        if let AtomicPropositionDerivationEvidence::Int32OnePlusStrictlyIncreases(step) = evidence {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: value,
                    right: sum,
                },
                true,
            ) = proposition
            else {
                return false;
            };
            let Bitvector32Term::Add(left, right) = sum.as_ref() else {
                return false;
            };
            let int_max = Bitvector32Term::Constant(i32::MAX as u32);
            return left.as_ref() == &Bitvector32Term::Constant(1)
                && right.as_ref() == value.as_ref()
                && step.lower == **value
                && step.upper == int_max
                && step.strict
                && self.checks_exact_order_step(step);
        }
        if let AtomicPropositionDerivationEvidence::Int32IncrementBelowMaxIsDefined(step) = evidence
        {
            let Proposition::ConditionIs(
                ConditionTerm::Overflows {
                    format: MachineIntegerType::Int32,
                    op: OverflowOperation::Add,
                    left: base,
                    right: amount,
                },
                false,
            ) = proposition
            else {
                return false;
            };
            let int_max = Bitvector32Term::Constant(i32::MAX as u32);
            return amount.as_ref() == &Bitvector32Term::Constant(1)
                && step.lower == **base
                && step.upper == int_max
                && step.strict
                && matches!(
                    &step.premise,
                    Proposition::ConditionIs(condition, value)
                        if self.exact_condition_value(condition) == Some(*value)
                            && condition_as_order_fact(condition, *value)
                                == Some((step.lower.clone(), step.upper.clone(), true))
                );
        }
        if let AtomicPropositionDerivationEvidence::Int32OnePlusBelowMaxIsDefined(step) = evidence {
            let Proposition::ConditionIs(
                ConditionTerm::Overflows {
                    format: MachineIntegerType::Int32,
                    op: OverflowOperation::Add,
                    left: one,
                    right: value,
                },
                false,
            ) = proposition
            else {
                return false;
            };
            let int_max = Bitvector32Term::Constant(i32::MAX as u32);
            return one.as_ref() == &Bitvector32Term::Constant(1)
                && step.lower == **value
                && step.upper == int_max
                && step.strict
                && self.checks_exact_order_step(step);
        }
        if let AtomicPropositionDerivationEvidence::Int32NonnegativeAddWithinMaxIsDefined(bounds) =
            evidence
        {
            let Proposition::ConditionIs(
                ConditionTerm::Overflows {
                    format: MachineIntegerType::Int32,
                    op: OverflowOperation::Add,
                    left: value,
                    right: amount,
                },
                false,
            ) = proposition
            else {
                return false;
            };
            let headroom = Bitvector32Term::Subtract(
                Box::new(Bitvector32Term::Constant(i32::MAX as u32)),
                Box::new(amount.as_ref().clone()),
            );
            return bounds.amount_nonnegative.lower == Bitvector32Term::Constant(0)
                && bounds.amount_nonnegative.upper == **amount
                && !bounds.amount_nonnegative.strict
                && bounds.within_headroom.lower == **value
                && bounds.within_headroom.upper == headroom
                && !bounds.within_headroom.strict
                && self.checks_exact_order_step(&bounds.amount_nonnegative)
                && self.checks_exact_order_step(&bounds.within_headroom);
        }
        if let AtomicPropositionDerivationEvidence::Int32NonnegativeSubtractWithinValueIsDefined(
            bounds,
        ) = evidence
        {
            let Proposition::ConditionIs(
                ConditionTerm::Overflows {
                    format: MachineIntegerType::Int32,
                    op: OverflowOperation::Subtract,
                    left: value,
                    right: amount,
                },
                false,
            ) = proposition
            else {
                return false;
            };
            return bounds.amount_nonnegative.lower == Bitvector32Term::Constant(0)
                && bounds.amount_nonnegative.upper == **amount
                && !bounds.amount_nonnegative.strict
                && bounds.within_value.lower == **amount
                && bounds.within_value.upper == **value
                && !bounds.within_value.strict
                && self.checks_exact_order_step(&bounds.amount_nonnegative)
                && self.checks_exact_order_step(&bounds.within_value);
        }
        if let AtomicPropositionDerivationEvidence::Int32IncrementLowerBound(bounds) = evidence {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: lower,
                    right: incremented,
                },
                true,
            ) = proposition
            else {
                return false;
            };
            let Some(base) = incremented.add_const_base(1) else {
                return false;
            };
            return self.checks_increment_bounds(bounds, lower, &base);
        }
        if let AtomicPropositionDerivationEvidence::Int32IncrementGreaterEqualLowerBound(bounds) =
            evidence
        {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterEqual,
                    left: incremented,
                    right: lower,
                },
                true,
            ) = proposition
            else {
                return false;
            };
            let Some(base) = incremented.add_const_base(1) else {
                return false;
            };
            return self.checks_increment_bounds(bounds, lower, &base);
        }
        if let AtomicPropositionDerivationEvidence::Int32IncrementStrictGreaterLowerBound(bounds) =
            evidence
        {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterThan,
                    left: incremented,
                    right: lower,
                },
                true,
            ) = proposition
            else {
                return false;
            };
            let Some(base) = incremented.add_const_base(1) else {
                return false;
            };
            return self.checks_increment_bounds(bounds, lower, &base);
        }
        if let AtomicPropositionDerivationEvidence::Int32IncrementStrictGreaterFromStrictLower(
            bounds,
        ) = evidence
        {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterThan,
                    left: incremented,
                    right: lower,
                },
                true,
            ) = proposition
            else {
                return false;
            };
            let Some(base) = incremented.add_const_base(1) else {
                return false;
            };
            return self.checks_strict_increment_bounds(bounds, lower, &base);
        }
        if let AtomicPropositionDerivationEvidence::Int32IncrementPreservesOrder(bounds) = evidence
        {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: incremented_lower,
                    right: incremented_value,
                },
                true,
            ) = proposition
            else {
                return false;
            };
            let Some((lower, value)) = incremented_lower
                .add_const_base(1)
                .zip(incremented_value.add_const_base(1))
            else {
                return false;
            };
            return self.checks_increment_bounds(bounds, &lower, &value);
        }
        if let AtomicPropositionDerivationEvidence::Int32PositiveIsNonnegative(step) = evidence {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: lower,
                    right: value,
                }
                | ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterEqual,
                    left: value,
                    right: lower,
                },
                true,
            ) = proposition
            else {
                return false;
            };
            return lower.as_ref() == &Bitvector32Term::Constant(0)
                && step.lower == Bitvector32Term::Constant(0)
                && step.upper == **value
                && step.strict
                && self.checks_exact_order_step(step);
        }
        if let AtomicPropositionDerivationEvidence::Int32SuccessorLeImpliesLt(step) = evidence {
            let (lower, value) = match proposition {
                Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left: lower,
                        right: value,
                    },
                    true,
                )
                | Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterThan,
                        left: value,
                        right: lower,
                    },
                    true,
                ) => (lower, value),
                _ => return false,
            };
            let Bitvector32Term::Constant(lower_bits) = lower.as_ref() else {
                return false;
            };
            let Some(successor_bits) = (*lower_bits as i32).checked_add(1) else {
                return false;
            };
            return step.lower == Bitvector32Term::Constant(successor_bits as u32)
                && step.upper == **value
                && !step.strict
                && self.checks_exact_order_step(step);
        }
        if let AtomicPropositionDerivationEvidence::Int32ConstantLowerBoundWeakening(step) =
            evidence
        {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: goal_lower,
                    right: value,
                },
                true,
            ) = proposition
            else {
                return false;
            };
            let (Bitvector32Term::Constant(goal_bits), Bitvector32Term::Constant(premise_bits)) =
                (goal_lower.as_ref(), &step.lower)
            else {
                return false;
            };
            return (*goal_bits as i32) < (*premise_bits as i32)
                && step.upper == **value
                && !step.strict
                && self.checks_exact_order_step(step);
        }
        if let AtomicPropositionDerivationEvidence::Int32NegatedStrictSuccessorBound(step) =
            evidence
        {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterEqual,
                    left: value,
                    right: lower,
                },
                true,
            ) = proposition
            else {
                return false;
            };
            let Bitvector32Term::Constant(lower_bits) = lower.as_ref() else {
                return false;
            };
            let Some(upper_bits) = (*lower_bits as i32).checked_add(1) else {
                return false;
            };
            let upper = Bitvector32Term::Constant(upper_bits as u32);
            return step.lower == upper
                && step.upper == **value
                && !step.strict
                && matches!(
                    &step.premise,
                    Proposition::ConditionIs(
                        ConditionTerm::Compare { format: MachineIntegerType::Int32, relation: CompareRelation::LessThan, left: premise_value, right: premise_upper },
                        false,
                    ) if premise_value.as_ref() == value.as_ref()
                        && premise_upper.as_ref() == &step.lower
                )
                && self.checks_exact_order_step(step);
        }
        if let AtomicPropositionDerivationEvidence::Int32PositivePredecessorIsNonnegative(step) =
            evidence
        {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: lower,
                    right: predecessor,
                },
                true,
            ) = proposition
            else {
                return false;
            };
            let Some(value) = exact_predecessor_base(predecessor) else {
                return false;
            };
            return lower.as_ref() == &Bitvector32Term::Constant(0)
                && step.lower == Bitvector32Term::Constant(0)
                && step.upper == value
                && step.strict
                && self.checks_exact_order_step(step);
        }
        if let AtomicPropositionDerivationEvidence::Int32PositivePredecessorStrictlyDecreases(
            step,
        ) = evidence
        {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: predecessor,
                    right: value,
                },
                true,
            ) = proposition
            else {
                return false;
            };
            let Some(base) = exact_predecessor_base(predecessor) else {
                return false;
            };
            return base == **value
                && step.lower == Bitvector32Term::Constant(0)
                && step.upper == base
                && step.strict
                && self.checks_exact_order_step(step);
        }
        if let AtomicPropositionDerivationEvidence::Int32NonnegativePredecessorUpperBound(bounds) =
            evidence
        {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: predecessor,
                    right: upper,
                },
                true,
            ) = proposition
            else {
                return false;
            };
            let Some(value) = exact_predecessor_base(predecessor) else {
                return false;
            };
            return bounds.nonnegative.lower == Bitvector32Term::Constant(0)
                && bounds.nonnegative.upper == value
                && !bounds.nonnegative.strict
                && bounds.upper_bound.lower == value
                && bounds.upper_bound.upper == **upper
                && !bounds.upper_bound.strict
                && self.checks_exact_order_step(&bounds.nonnegative)
                && self.checks_exact_order_step(&bounds.upper_bound);
        }
        if let AtomicPropositionDerivationEvidence::Int32OneLePredecessorIsNonnegative(source) =
            evidence
        {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: lower,
                    right: predecessor,
                },
                true,
            ) = proposition
            else {
                return false;
            };
            let Some(value) = exact_predecessor_base(predecessor) else {
                return false;
            };
            return lower.as_ref() == &Bitvector32Term::Constant(0)
                && self.checks_one_le_evidence(source, &value);
        }
        if let AtomicPropositionDerivationEvidence::Int32OneLePredecessorStrictlyDecreases(source) =
            evidence
        {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: predecessor,
                    right: value,
                },
                true,
            ) = proposition
            else {
                return false;
            };
            let Some(base) = exact_predecessor_base(predecessor) else {
                return false;
            };
            return base == **value && self.checks_one_le_evidence(source, &base);
        }
        if let AtomicPropositionDerivationEvidence::Int32EqualOnePredecessorIsZero(path) = evidence
        {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                true,
            ) = proposition
            else {
                return false;
            };
            let Some(value) = exact_predecessor_equal_zero_base(left, right) else {
                return false;
            };
            return self.checks_exact_bitvector_equality_path(
                path,
                &value,
                &Bitvector32Term::Constant(1),
            );
        }
        if let AtomicPropositionDerivationEvidence::Int32PinnedConstantEquality(evidence) = evidence
        {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                true,
            ) = proposition
            else {
                return false;
            };
            return evidence.checks(left, right, self);
        }
        if let AtomicPropositionDerivationEvidence::Int32LeAndNotLtImpliesEquality(evidence) =
            evidence
        {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                true,
            ) = proposition
            else {
                return false;
            };
            let less_equal =
                ConditionTerm::signed_less_equal(left.as_ref().clone(), right.as_ref().clone());
            let less_than =
                ConditionTerm::signed_less_than(left.as_ref().clone(), right.as_ref().clone());
            return evidence.less_equal == Proposition::ConditionIs(less_equal, true)
                && evidence.not_less_than == Proposition::ConditionIs(less_than, false)
                && self.contains_assumed_exact(&evidence.less_equal)
                && self.contains_assumed_exact(&evidence.not_less_than);
        }
        if let AtomicPropositionDerivationEvidence::Int32GeAndNotGtImpliesEquality(evidence) =
            evidence
        {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                true,
            ) = proposition
            else {
                return false;
            };
            let greater_equal =
                ConditionTerm::signed_greater_equal(left.as_ref().clone(), right.as_ref().clone());
            let greater_than =
                ConditionTerm::signed_greater_than(left.as_ref().clone(), right.as_ref().clone());
            return evidence.greater_equal == Proposition::ConditionIs(greater_equal, true)
                && evidence.not_greater_than == Proposition::ConditionIs(greater_than, false)
                && self.contains_assumed_exact(&evidence.greater_equal)
                && self.contains_assumed_exact(&evidence.not_greater_than);
        }
        if let AtomicPropositionDerivationEvidence::Int32LeAndNeqImpliesStrict(evidence) = evidence
        {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left,
                    right,
                },
                true,
            ) = proposition
            else {
                return false;
            };
            let less_equal = Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(left.as_ref().clone(), right.as_ref().clone()),
                true,
            );
            let not_equal = Proposition::ConditionIs(
                ConditionTerm::equal(left.as_ref().clone(), right.as_ref().clone()),
                false,
            );
            return evidence.less_equal == less_equal
                && evidence.not_equal == not_equal
                && self.contains_assumed_exact(&evidence.less_equal)
                && self.contains_assumed_exact(&evidence.not_equal);
        }
        if let Some(result) = ATOMIC_DERIVATION_MEMO.with(|memo| {
            memo.borrow()
                .get(&atomic_derivation_memo_key(premises_id, for_simp))
                .and_then(|entries| entries.get(proposition))
                .cloned()
        }) {
            return result.is_some();
        }
        self.proves_atomic_for_derivation(proposition, for_simp)
    }

    /// The signed-order bound entries for a term, looked up under its own
    /// term and, when different, its canonical form. Each entry yields the
    /// fact's own endpoint term first, so callers can cite the exact fact
    /// even when the query reached it through the canonical form.
    pub(crate) fn signed_order_bound_entries(
        &self,
        term: &Bitvector32Term,
    ) -> impl Iterator<Item = (Bitvector32Term, Bitvector32Term, bool, bool)> + '_ {
        let direct = self.signed_order_bounds.get(term);
        let alias = {
            let canonical = crate::kernel::eval::canonical_term(term);
            if &canonical == term {
                None
            } else {
                self.signed_order_bounds.get(&canonical)
            }
        };
        direct
            .into_iter()
            .chain(alias)
            .flat_map(|bounds| bounds.keys())
            .map(|(fact_endpoint, other, strict, forward)| {
                (fact_endpoint.clone(), other.clone(), *strict, *forward)
            })
    }

    fn exact_direct_strict_upper_bound_step(
        &self,
        base: &Bitvector32Term,
    ) -> Option<SignedOrderDerivationStep> {
        self.signed_order_bound_entries(base)
            .filter(|(_, _, strict, forward)| *strict && *forward)
            .find_map(|(fact_endpoint, upper, _, _)| {
                self.exact_direct_order_step(&fact_endpoint, &upper, true)
            })
    }

    /// Whether one recorded order fact bounds `lower` by `upper` (strictly
    /// when `strict`), joining both endpoints by canonical form through the
    /// dual-keyed bounds index. Indexed and deterministic: a cheap answer
    /// for range checks before any searching arm runs.
    pub(in crate::kernel) fn canonical_bound_holds(
        &self,
        lower: &Bitvector32Term,
        upper: &Bitvector32Term,
        strict: bool,
    ) -> bool {
        self.signed_order_bound_entries(lower)
            .any(|(_, other, entry_strict, forward)| {
                forward
                    && (entry_strict || !strict)
                    && crate::kernel::eval::terms_have_same_canonical_form(&other, upper)
            })
            || self
                .signed_order_bound_entries(upper)
                .any(|(_, other, entry_strict, forward)| {
                    !forward
                        && (entry_strict || !strict)
                        && crate::kernel::eval::terms_have_same_canonical_form(&other, lower)
                })
    }

    pub(in crate::kernel) fn exact_direct_order_step(
        &self,
        lower: &Bitvector32Term,
        upper: &Bitvector32Term,
        strict: bool,
    ) -> Option<SignedOrderDerivationStep> {
        let candidates = if strict {
            [
                (
                    ConditionTerm::signed_less_than(lower.clone(), upper.clone()),
                    true,
                ),
                (
                    ConditionTerm::signed_less_equal(upper.clone(), lower.clone()),
                    false,
                ),
                (
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterThan,
                        left: Box::new(upper.clone()),
                        right: Box::new(lower.clone()),
                    },
                    true,
                ),
                (
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterEqual,
                        left: Box::new(lower.clone()),
                        right: Box::new(upper.clone()),
                    },
                    false,
                ),
            ]
        } else {
            [
                (
                    ConditionTerm::signed_less_equal(lower.clone(), upper.clone()),
                    true,
                ),
                (
                    ConditionTerm::signed_less_than(upper.clone(), lower.clone()),
                    false,
                ),
                (
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterEqual,
                        left: Box::new(upper.clone()),
                        right: Box::new(lower.clone()),
                    },
                    true,
                ),
                (
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterThan,
                        left: Box::new(lower.clone()),
                        right: Box::new(upper.clone()),
                    },
                    false,
                ),
            ]
        };
        candidates
            .into_iter()
            .find(|(condition, truth)| {
                crate::instrumentation::record_deterministic_work(1);
                self.condition_facts.get(condition) == Some(truth)
            })
            .map(|(condition, truth)| SignedOrderDerivationStep {
                lower: lower.clone(),
                upper: upper.clone(),
                strict,
                premise: Proposition::ConditionIs(condition, truth),
            })
    }

    fn exact_one_le_evidence(&self, value: &Bitvector32Term) -> Option<Int32OneLeEvidence> {
        self.exact_bitvector_equality_path_evidence(value, &Bitvector32Term::Constant(1))
            .map(Int32OneLeEvidence::EqualOne)
            .or_else(|| {
                self.exact_direct_order_step(&Bitvector32Term::Constant(1), value, false)
                    .map(Box::new)
                    .map(Int32OneLeEvidence::Direct)
            })
    }

    pub(in crate::kernel) fn checks_exact_bitvector_equality_path(
        &self,
        path: &[BitvectorEqualityDerivationStep],
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let mut current = left;
        for step in path {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: premise_left,
                    right: premise_right,
                },
                true,
            ) = &step.premise
            else {
                return false;
            };
            if current != &step.source
                || self.exact_condition_value(&ConditionTerm::equal(
                    premise_left.as_ref().clone(),
                    premise_right.as_ref().clone(),
                )) != Some(true)
                || !((step.source == **premise_left && step.target == **premise_right)
                    || (step.source == **premise_right && step.target == **premise_left))
            {
                return false;
            }
            current = &step.target;
        }
        current == right
    }

    fn checks_one_le_evidence(&self, source: &Int32OneLeEvidence, value: &Bitvector32Term) -> bool {
        match source {
            Int32OneLeEvidence::Direct(step) => {
                step.lower == Bitvector32Term::Constant(1)
                    && step.upper == *value
                    && !step.strict
                    && self.checks_exact_order_step(step)
            }
            Int32OneLeEvidence::EqualOne(path) => self.checks_exact_bitvector_equality_path(
                path,
                value,
                &Bitvector32Term::Constant(1),
            ),
        }
    }

    fn exact_increment_bounds_evidence(
        &self,
        lower: &Bitvector32Term,
        value: &Bitvector32Term,
    ) -> Option<Box<Int32IncrementBoundsEvidence>> {
        let lower_bound = self.exact_direct_order_step(lower, value, false)?;
        let upper_bound = self.exact_direct_strict_upper_bound_step(value)?;
        Some(Box::new(Int32IncrementBoundsEvidence {
            lower_bound,
            upper_bound,
        }))
    }

    fn exact_strict_increment_bounds_evidence(
        &self,
        lower: &Bitvector32Term,
        value: &Bitvector32Term,
    ) -> Option<Box<Int32IncrementBoundsEvidence>> {
        let lower_bound = self.exact_direct_order_step(lower, value, true)?;
        let upper_bound = self.exact_direct_strict_upper_bound_step(value)?;
        Some(Box::new(Int32IncrementBoundsEvidence {
            lower_bound,
            upper_bound,
        }))
    }

    fn checks_increment_bounds(
        &self,
        bounds: &Int32IncrementBoundsEvidence,
        lower: &Bitvector32Term,
        value: &Bitvector32Term,
    ) -> bool {
        bounds.lower_bound.lower == *lower
            && bounds.lower_bound.upper == *value
            && !bounds.lower_bound.strict
            && bounds.upper_bound.lower == *value
            && bounds.upper_bound.strict
            && self.checks_exact_order_step(&bounds.lower_bound)
            && self.checks_exact_order_step(&bounds.upper_bound)
    }

    fn checks_strict_increment_bounds(
        &self,
        bounds: &Int32IncrementBoundsEvidence,
        lower: &Bitvector32Term,
        value: &Bitvector32Term,
    ) -> bool {
        bounds.lower_bound.lower == *lower
            && bounds.lower_bound.upper == *value
            && bounds.lower_bound.strict
            && bounds.upper_bound.lower == *value
            && bounds.upper_bound.strict
            && self.checks_exact_order_step(&bounds.lower_bound)
            && self.checks_exact_order_step(&bounds.upper_bound)
    }

    pub(in crate::kernel) fn checks_exact_order_step(
        &self,
        step: &SignedOrderDerivationStep,
    ) -> bool {
        matches!(
            &step.premise,
            Proposition::ConditionIs(condition, truth)
                if self.exact_condition_value(condition) == Some(*truth)
                    && condition_as_order_fact(condition, *truth)
                        == Some((step.lower.clone(), step.upper.clone(), step.strict))
        )
    }

    /// Checks one retained signed-order path using only its exact named
    /// premises. This mirrors `exact_signed_order_path_evidence`'s terminal
    /// constant comparison but never searches the ambient order graph.
    pub(in crate::kernel) fn checks_exact_signed_order_path(
        &self,
        path: &[SignedOrderDerivationStep],
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        require_strict: bool,
    ) -> bool {
        if path.is_empty() {
            return false;
        }
        let mut current = left;
        let mut strict = false;
        for step in path {
            if current != &step.lower {
                // A normalized direct premise can start at a successor
                // literal (1 < n becomes 2 <= n). Retain that intrinsic
                // connection just as the final literal connection below.
                let Some(connection) = signed_bitvector_constant(current)
                    .zip(signed_bitvector_constant(&step.lower))
                    .and_then(|(current, next)| (current <= next).then_some(current < next))
                else {
                    return false;
                };
                strict |= connection;
            }
            if !self.checks_exact_order_step(step) {
                return false;
            }
            current = &step.upper;
            strict |= step.strict;
        }
        let constant_connection = signed_bitvector_constant(current)
            .zip(signed_bitvector_constant(right))
            .and_then(|(current, right)| (current <= right).then_some(current < right));
        (current == right || constant_connection.is_some())
            && (!require_strict || strict || constant_connection == Some(true))
    }

    pub(super) fn checks_forall_loadable_range(
        &self,
        proposition: &Proposition,
        source: &Proposition,
    ) -> bool {
        let Some((premises, conclusion)) = forall_loadable_range_parts(proposition) else {
            return false;
        };
        let Proposition::CMemoryLoadable { bytes, .. } = conclusion else {
            return false;
        };
        if bytes.as_const() != Some(1) || !self.proves_exact(source) {
            return false;
        }
        let mut candidate = PureFactContext::new().assume_proposition(source.clone());
        for premise in premises {
            candidate = candidate.assume_proposition(premise);
        }
        crate::kernel::api::loadable_covered_by_fact(&candidate, conclusion)
    }

    pub(super) fn checks_exists_loadable_range(
        &self,
        proposition: &Proposition,
        source: &Proposition,
        witness: &Bitvector32Term,
    ) -> bool {
        let Proposition::Exists {
            var,
            sort: Sort::CInt32,
            body,
            ..
        } = proposition
        else {
            return false;
        };
        if witness != &Bitvector32Term::Constant(0)
            || !self.proves_exact(source)
            || !matches!(source, Proposition::CMemoryLoadable { .. })
        {
            return false;
        }
        let instantiated = substitute_bitvector_variable_in_proposition(body, *var, witness);
        if !matches!(instantiated, Proposition::CMemoryLoadable { .. }) {
            return false;
        }
        let mut candidate = self.clone();
        candidate.clear_proposition_facts();
        candidate.insert_proposition_fact(source.clone());
        crate::kernel::api::loadable_covered_by_fact(&candidate, &instantiated)
    }

    pub(crate) fn proves_condition_from_facts(
        &self,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        self.condition_facts
            .iter()
            .any(|(fact_condition, fact_value)| {
                fact_value == &value && self.condition_matches(fact_condition, condition)
            })
            || self
                .prop_facts
                .iter()
                .any(|proposition| self.proposition_proves_condition(proposition, condition, value))
            || self.proves_condition_from_derived_order_facts(condition, value)
    }

    pub(in crate::kernel) fn proves_condition_from_derived_order_facts(
        &self,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        let Some((left, right, strict)) = condition_as_order_fact(condition, value) else {
            return false;
        };
        // Order facts come from `condition_facts` only. A bound that lives
        // inside a guarded implication or a finite universal reaches this
        // theory through an explicit `intro`, `extract`, or `enumerate` step,
        // or through the exact conjunction split `assume_proposition`
        // performs; deriving it here meant discharging antecedents with the
        // general prover and instantiating quantifiers inside a theory query.
        self.difference_graph_proves_order(&left, &right, strict)
    }

    /// The universal proposition facts, in `prop_facts` order, charged one
    /// unit each: only these can be instantiated or alpha-renamed.
    pub(in crate::kernel) fn quantified_fact_propositions(
        &self,
    ) -> impl Iterator<Item = &Proposition> {
        self.atomic_quantified_facts.iter().map(|fact| {
            crate::instrumentation::record_deterministic_work(1);
            fact.as_ref()
        })
    }

    pub(super) fn collect_quantified_order_facts_for_condition(
        &self,
        condition: &ConditionTerm,
        order_facts: &mut Vec<(Bitvector32Term, Bitvector32Term, bool)>,
    ) {
        for proposition in self.quantified_fact_propositions() {
            for instance in self.forall_instantiations_for_condition(proposition, condition) {
                self.collect_derived_order_facts_from_proposition(&instance, order_facts);
            }
        }
    }

    pub(crate) fn proposition_proves_condition(
        &self,
        proposition: &Proposition,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        match proposition {
            Proposition::ConditionIs(fact_condition, fact_value) => {
                fact_value == &value && self.condition_matches(fact_condition, condition)
            }
            Proposition::And(left, right) => {
                self.proposition_proves_condition(left, condition, value)
                    || self.proposition_proves_condition(right, condition, value)
            }
            Proposition::Implies(left, right) => {
                // Most accumulated call facts conclude something unrelated
                // to this target.  Inspect the conclusion first; conjunction
                // is commutative, and this avoids a global antecedent proof
                // for every irrelevant implication in a long call chain.
                self.proposition_proves_condition(right, condition, value) && {
                    #[cfg(test)]
                    CONDITION_IMPLICATION_ANTECEDENT_CHECKS
                        .with(|checks| checks.set(checks.get() + 1));
                    self.proves_without_prop_facts(left)
                }
            }
            Proposition::ForAll { body, .. } => {
                self.proposition_proves_condition(body, condition, value)
                    || self
                        .forall_instantiations_for_condition(proposition, condition)
                        .iter()
                        .any(|body| self.proposition_proves_condition(body, condition, value))
                    || self
                        .finite_forall_instantiations(proposition)
                        .any(|body| self.proposition_proves_condition(&body, condition, value))
            }
            _ => false,
        }
    }

    pub(crate) fn finite_forall_instantiations<'a>(
        &self,
        proposition: &'a Proposition,
    ) -> impl Iterator<Item = Proposition> + 'a {
        finite_forall_goal_instances(proposition, false)
            .into_iter()
            .flatten()
            .map(|(_, instance)| instance)
    }

    /// The consequents of this context's universal implications, instantiated
    /// where `condition` names their bound variable and their antecedent is
    /// proved here. One scan of the universal facts; each candidate costs its
    /// own antecedent.
    pub(in crate::kernel) fn instantiated_universal_consequents(
        &self,
        condition: &ConditionTerm,
    ) -> Vec<Proposition> {
        let mut consequents = Vec::new();
        for proposition in self.quantified_fact_propositions() {
            for instance in self.forall_instantiations_for_condition(proposition, condition) {
                if let Proposition::Implies(antecedent, consequent) = instance
                    && self.proves_without_prop_facts(&antecedent)
                {
                    consequents.push(*consequent);
                }
            }
        }
        consequents
    }

    pub(in crate::kernel) fn forall_instantiations_for_condition(
        &self,
        proposition: &Proposition,
        condition: &ConditionTerm,
    ) -> Vec<Proposition> {
        let Proposition::ForAll { var, body, .. } = proposition else {
            return Vec::new();
        };
        Self::guided_forall_condition_candidates(*var, body, condition)
            .into_iter()
            .map(|candidate| substitute_bitvector_variable_in_proposition(body, *var, &candidate))
            .collect()
    }

    /// Guided instantiation candidates for one universal int32 body against a
    /// target condition: bound-variable subterm matches inside the body's
    /// conclusion, with scalar candidates retained for intermediate order bounds.
    pub(crate) fn guided_forall_condition_candidates(
        var: Variable,
        body: &Proposition,
        condition: &ConditionTerm,
    ) -> BTreeSet<Bitvector32Term> {
        fn collect_offset_candidates(
            pattern: &PointerOffsetTerm,
            target: &PointerOffsetTerm,
            bound: Variable,
            candidates: &mut BTreeSet<Bitvector32Term>,
        ) {
            if crate::kernel::reasoning::substitute_bitvector_variable_in_pointer_offset(
                pattern,
                bound,
                &Bitvector32Term::Constant(0),
            ) == *target
            {
                candidates.insert(Bitvector32Term::Constant(0));
            }
            match (pattern, target) {
                (
                    PointerOffsetTerm::Add(left_a, left_b),
                    PointerOffsetTerm::Add(right_a, right_b),
                ) => {
                    collect_offset_candidates(left_a, right_a, bound, candidates);
                    collect_offset_candidates(left_b, right_b, bound, candidates);
                }
                (
                    PointerOffsetTerm::Int32Scaled {
                        value: left,
                        byte_width: left_width,
                    },
                    PointerOffsetTerm::Int32Scaled {
                        value: right,
                        byte_width: right_width,
                    },
                ) if left_width == right_width => {
                    collect_term_candidates(left, right, bound, candidates);
                }
                (
                    PointerOffsetTerm::Int32Scaled {
                        value: left,
                        byte_width,
                    },
                    PointerOffsetTerm::Constant(bytes),
                ) if *byte_width != 0 && bytes % byte_width == 0 => {
                    let elements = bytes / byte_width;
                    collect_term_candidates(
                        left,
                        &Bitvector32Term::Constant((elements as i32) as u32),
                        bound,
                        candidates,
                    );
                }
                (
                    PointerOffsetTerm::Int64Scaled {
                        value: left,
                        byte_width: left_width,
                        unsigned: left_unsigned,
                    },
                    PointerOffsetTerm::Int64Scaled {
                        value: right,
                        byte_width: right_width,
                        unsigned: right_unsigned,
                    },
                ) if left_width == right_width && left_unsigned == right_unsigned => {
                    collect_term_candidates(left, right, bound, candidates);
                }
                (
                    PointerOffsetTerm::Int64Scaled {
                        value: left,
                        byte_width,
                        unsigned,
                    },
                    PointerOffsetTerm::Constant(bytes),
                ) if *byte_width != 0 && bytes % byte_width == 0 => {
                    let elements = bytes / byte_width;
                    let value = if *unsigned {
                        let Ok(elements) = u64::try_from(elements) else {
                            return;
                        };
                        Bitvector32Term::UInt64Constant(elements)
                    } else {
                        Bitvector32Term::Int64Constant(elements)
                    };
                    collect_term_candidates(left, &value, bound, candidates);
                }
                _ => {}
            }
        }
        fn collect_pointer_candidates(
            pattern: &Pointer,
            target: &Pointer,
            bound: Variable,
            candidates: &mut BTreeSet<Bitvector32Term>,
        ) {
            if pattern.block == target.block {
                collect_offset_candidates(&pattern.offset, &target.offset, bound, candidates);
            }
        }
        fn collect_term_candidates(
            pattern: &Bitvector32Term,
            target: &Bitvector32Term,
            bound: Variable,
            candidates: &mut BTreeSet<Bitvector32Term>,
        ) {
            if matches!(pattern, Bitvector32Term::Variable(variable) if *variable == bound) {
                candidates.insert(target.clone());
                return;
            }
            // A load variable represents a load. Match it as that load so a
            // universal over array cells
            // instantiates against a cell read under the creation-time
            // invariant exactly as against a load term.
            let pattern_load = crate::kernel::eval::viewed_as_memory_load(pattern);
            let target_load = crate::kernel::eval::viewed_as_memory_load(target);
            if let (Some(pattern_load), Some(target_load)) = (&pattern_load, &target_load)
                && (pattern_load != pattern || target_load != target)
            {
                collect_term_candidates(pattern_load, target_load, bound, candidates);
                return;
            }
            if std::mem::discriminant(pattern) != std::mem::discriminant(target) {
                return;
            }
            fn binary(term: &Bitvector32Term) -> Option<(&Bitvector32Term, &Bitvector32Term)> {
                match term {
                    crate::kernel::binary_bitvector32_term!(left, right) => {
                        Some((left.as_ref(), right.as_ref()))
                    }
                    _ => None,
                }
            }
            match (pattern, target) {
                (Bitvector32Term::BitwiseNot(left), Bitvector32Term::BitwiseNot(right)) => {
                    collect_term_candidates(left, right, bound, candidates);
                }
                (
                    Bitvector32Term::MemoryLoad(_, left_pointer, left_kind),
                    Bitvector32Term::MemoryLoad(_, right_pointer, right_kind),
                ) if left_kind == right_kind => {
                    collect_pointer_candidates(left_pointer, right_pointer, bound, candidates)
                }
                (left, right) => {
                    if let (Some((left_a, left_b)), Some((right_a, right_b))) =
                        (binary(left), binary(right))
                    {
                        collect_term_candidates(left_a, right_a, bound, candidates);
                        collect_term_candidates(left_b, right_b, bound, candidates);
                    }
                }
            }
        }
        fn collect_condition_candidates(
            pattern: &ConditionTerm,
            target: &ConditionTerm,
            bound: Variable,
            candidates: &mut BTreeSet<Bitvector32Term>,
        ) {
            match (pattern, target) {
                (
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left: pattern_left,
                        right: pattern_right,
                    },
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left: target_left,
                        right: target_right,
                    },
                )
                | (
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessEqual,
                        left: pattern_left,
                        right: pattern_right,
                    },
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessEqual,
                        left: target_left,
                        right: target_right,
                    },
                )
                | (
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterThan,
                        left: pattern_left,
                        right: pattern_right,
                    },
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterThan,
                        left: target_left,
                        right: target_right,
                    },
                )
                | (
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterEqual,
                        left: pattern_left,
                        right: pattern_right,
                    },
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterEqual,
                        left: target_left,
                        right: target_right,
                    },
                )
                | (
                    ConditionTerm::Overflows {
                        format: MachineIntegerType::Int32,
                        op: OverflowOperation::Add,
                        left: pattern_left,
                        right: pattern_right,
                    },
                    ConditionTerm::Overflows {
                        format: MachineIntegerType::Int32,
                        op: OverflowOperation::Add,
                        left: target_left,
                        right: target_right,
                    },
                )
                | (
                    ConditionTerm::Overflows {
                        format: MachineIntegerType::Int32,
                        op: OverflowOperation::Subtract,
                        left: pattern_left,
                        right: pattern_right,
                    },
                    ConditionTerm::Overflows {
                        format: MachineIntegerType::Int32,
                        op: OverflowOperation::Subtract,
                        left: target_left,
                        right: target_right,
                    },
                )
                | (
                    ConditionTerm::Overflows {
                        format: MachineIntegerType::Int32,
                        op: OverflowOperation::Multiply,
                        left: pattern_left,
                        right: pattern_right,
                    },
                    ConditionTerm::Overflows {
                        format: MachineIntegerType::Int32,
                        op: OverflowOperation::Multiply,
                        left: target_left,
                        right: target_right,
                    },
                )
                | (
                    ConditionTerm::Overflows {
                        format: MachineIntegerType::Int32,
                        op: OverflowOperation::Divide,
                        left: pattern_left,
                        right: pattern_right,
                    },
                    ConditionTerm::Overflows {
                        format: MachineIntegerType::Int32,
                        op: OverflowOperation::Divide,
                        left: target_left,
                        right: target_right,
                    },
                )
                | (
                    ConditionTerm::Overflows {
                        format: MachineIntegerType::Int32,
                        op: OverflowOperation::ShiftLeft,
                        left: pattern_left,
                        right: pattern_right,
                    },
                    ConditionTerm::Overflows {
                        format: MachineIntegerType::Int32,
                        op: OverflowOperation::ShiftLeft,
                        left: target_left,
                        right: target_right,
                    },
                ) => {
                    collect_term_candidates(pattern_left, target_left, bound, candidates);
                    collect_term_candidates(pattern_right, target_right, bound, candidates);
                }
                (
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: pattern_left,
                        right: pattern_right,
                    },
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: target_left,
                        right: target_right,
                    },
                ) => {
                    collect_term_candidates(pattern_left, target_left, bound, candidates);
                    collect_term_candidates(pattern_right, target_right, bound, candidates);
                    collect_term_candidates(pattern_left, target_right, bound, candidates);
                    collect_term_candidates(pattern_right, target_left, bound, candidates);
                }
                (
                    ConditionTerm::PointerOffsetEqual(pattern_left, pattern_right),
                    ConditionTerm::PointerOffsetEqual(target_left, target_right),
                ) => {
                    collect_offset_candidates(pattern_left, target_left, bound, candidates);
                    collect_offset_candidates(pattern_right, target_right, bound, candidates);
                    collect_offset_candidates(pattern_left, target_right, bound, candidates);
                    collect_offset_candidates(pattern_right, target_left, bound, candidates);
                }
                (
                    ConditionTerm::PointerEqual(pattern_left, pattern_right),
                    ConditionTerm::PointerEqual(target_left, target_right),
                ) => {
                    collect_pointer_candidates(pattern_left, target_left, bound, candidates);
                    collect_pointer_candidates(pattern_right, target_right, bound, candidates);
                    collect_pointer_candidates(pattern_left, target_right, bound, candidates);
                    collect_pointer_candidates(pattern_right, target_left, bound, candidates);
                }
                _ => {}
            }
        }
        fn collect_proposition_condition_candidates(
            proposition: &Proposition,
            target: &ConditionTerm,
            bound: Variable,
            candidates: &mut BTreeSet<Bitvector32Term>,
        ) {
            match proposition {
                Proposition::ConditionIs(pattern, _) => {
                    collect_condition_candidates(pattern, target, bound, candidates)
                }
                Proposition::And(left, right) => {
                    collect_proposition_condition_candidates(left, target, bound, candidates);
                    collect_proposition_condition_candidates(right, target, bound, candidates);
                }
                _ => {}
            }
        }
        let mut candidates = BTreeSet::new();
        // Order reasoning also uses intermediate bounds whose other endpoint
        // need not match the requested condition. Keep its scalar candidates;
        // equality transport must match a bound occurrence instead of trying
        // every unrelated scalar as an array index.
        if !matches!(
            condition,
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                ..
            }
        ) {
            let mut variables = BTreeSet::new();
            collect_condition_bitvector_variables(condition, &mut variables);
            candidates.extend(variables.into_iter().map(Bitvector32Term::Variable));
        }
        let conclusion = match body {
            Proposition::Implies(_, conclusion) => conclusion.as_ref(),
            conclusion => conclusion,
        };
        collect_proposition_condition_candidates(conclusion, condition, var, &mut candidates);
        candidates
    }

    pub(in crate::kernel) fn condition_matches(
        &self,
        fact: &ConditionTerm,
        target: &ConditionTerm,
    ) -> bool {
        if fact == target {
            return true;
        }

        match (fact, target) {
            (
                ConditionTerm::IntegerEqual(fact_left, fact_right),
                ConditionTerm::IntegerEqual(target_left, target_right),
            ) => fact_left == target_right && fact_right == target_left,
            (
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: fact_left,
                    right: fact_right,
                },
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: target_left,
                    right: target_right,
                },
            ) => {
                let fact_left = fact_left.as_ref();
                let fact_right = fact_right.as_ref();
                let target_left = target_left.as_ref();
                let target_right = target_right.as_ref();
                fact_right == target_right
                    && self.bitvector_terms_equal_for_transport(fact_left, target_left)
                    || fact_right == target_left
                        && self.bitvector_terms_equal_for_transport(fact_left, target_right)
                    || fact_left == target_right
                        && self.bitvector_terms_equal_for_transport(fact_right, target_left)
                    || fact_left == target_left
                        && self.bitvector_terms_equal_for_transport(fact_right, target_right)
                    || self.bitvector_terms_equal_for_transport(fact_left, target_left)
                        && self.bitvector_terms_equal_for_transport(fact_right, target_right)
                    || self.bitvector_terms_equal_for_transport(fact_left, target_right)
                        && self.bitvector_terms_equal_for_transport(fact_right, target_left)
            }
            // A pointer-value fact carries operand by operand, each pair one
            // value as the snapshot-modulo matchers read it: the same
            // designation, at a proven-equal address or as one complete read
            // across the frame (`n->right` before a call, `old(n)->right`
            // after it).
            (
                ConditionTerm::PointerValueEqual(fact_left, fact_right),
                ConditionTerm::PointerValueEqual(target_left, target_right),
            ) => {
                let same = |fact: &crate::kernel::CPointerValue,
                            target: &crate::kernel::CPointerValue| {
                    fact == target
                        || fact.c_type() == target.c_type()
                            && self.pointer_designations_match(fact, target)
                            && (crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
                                fact.pointer(),
                                target.pointer(),
                                self,
                            ) || crate::kernel::memory_provenance::complete_pointer_reads_equal_across_frame(
                                fact.pointer(),
                                target.pointer(),
                                self,
                            ))
                };
                same(fact_left, target_left) && same(fact_right, target_right)
                    || same(fact_left, target_right) && same(fact_right, target_left)
            }
            (
                ConditionTerm::PointerOffsetEqual(fact_left, fact_right),
                ConditionTerm::PointerOffsetEqual(target_left, target_right),
            ) => {
                let fact_left = fact_left.as_ref();
                let fact_right = fact_right.as_ref();
                let target_left = target_left.as_ref();
                let target_right = target_right.as_ref();
                fact_right == target_right
                    && self.pointer_offset_terms_equal_for_transport(fact_left, target_left)
                    || fact_right == target_left
                        && self.pointer_offset_terms_equal_for_transport(fact_left, target_right)
                    || fact_left == target_right
                        && self.pointer_offset_terms_equal_for_transport(fact_right, target_left)
                    || fact_left == target_left
                        && self.pointer_offset_terms_equal_for_transport(fact_right, target_right)
                    || self.pointer_offset_terms_snapshot_equivalent(fact_left, target_left)
                        && self.pointer_offset_terms_snapshot_equivalent(fact_right, target_right)
                    || self.pointer_offset_terms_snapshot_equivalent(fact_left, target_right)
                        && self.pointer_offset_terms_snapshot_equivalent(fact_right, target_left)
            }
            (
                ConditionTerm::Overflows {
                    format: MachineIntegerType::Int32,
                    op: OverflowOperation::Add,
                    left: fact_left,
                    right: fact_right,
                },
                ConditionTerm::Overflows {
                    format: MachineIntegerType::Int32,
                    op: OverflowOperation::Add,
                    left: target_left,
                    right: target_right,
                },
            ) => {
                self.bitvector_terms_equal_for_transport(fact_left, target_left)
                    && self.bitvector_terms_equal_for_transport(fact_right, target_right)
                    || self.bitvector_terms_equal_for_transport(fact_left, target_right)
                        && self.bitvector_terms_equal_for_transport(fact_right, target_left)
            }
            (
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: fact_left,
                    right: fact_right,
                },
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: target_left,
                    right: target_right,
                },
            )
            | (
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: fact_left,
                    right: fact_right,
                },
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: target_left,
                    right: target_right,
                },
            )
            | (
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterThan,
                    left: fact_left,
                    right: fact_right,
                },
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterThan,
                    left: target_left,
                    right: target_right,
                },
            )
            | (
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterEqual,
                    left: fact_left,
                    right: fact_right,
                },
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterEqual,
                    left: target_left,
                    right: target_right,
                },
            ) => self.comparison_sides_equal_for_transport(
                fact_left,
                fact_right,
                target_left,
                target_right,
            ),
            (
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: fact_left,
                    right: fact_right,
                },
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterThan,
                    left: target_left,
                    right: target_right,
                },
            )
            | (
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterThan,
                    left: fact_left,
                    right: fact_right,
                },
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: target_left,
                    right: target_right,
                },
            )
            | (
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: fact_left,
                    right: fact_right,
                },
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterEqual,
                    left: target_left,
                    right: target_right,
                },
            )
            | (
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterEqual,
                    left: fact_left,
                    right: fact_right,
                },
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: target_left,
                    right: target_right,
                },
            ) => self.comparison_sides_equal_for_transport(
                fact_left,
                fact_right,
                target_right,
                target_left,
            ),
            _ => false,
        }
    }

    fn comparison_sides_equal_for_transport(
        &self,
        fact_left: &Bitvector32Term,
        fact_right: &Bitvector32Term,
        target_left: &Bitvector32Term,
        target_right: &Bitvector32Term,
    ) -> bool {
        // Check a literal bound before registering a possibly large model
        // getter on the other side. The equality judgments are unchanged;
        // a mismatched bound makes visiting that payload unnecessary.
        let (first_fact, first_target, second_fact, second_target) =
            if matches!(fact_right, Bitvector32Term::Constant(_)) {
                (fact_right, target_right, fact_left, target_left)
            } else {
                (fact_left, target_left, fact_right, target_right)
            };
        self.bitvector_terms_equal_for_transport(first_fact, first_target)
            && self.bitvector_terms_equal_for_transport(second_fact, second_target)
    }

    /// Broader expression reasoning, including conditionals, folds, and
    /// checked memory resolution. Maintained int32 equality is queried through
    /// `int32_values_known_equal` without invoking these rules.
    pub(in crate::kernel) fn bitvector_terms_proven_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        left == right
            || self.bitvector_if_terms_proven_equal(left, right)
            || self.bitvector_add_terms_proven_equal(left, right)
            || self.count_fold_split_terms_proven_equal(left, right)
            || self.range_fold_terms_alpha_equivalent(left, right)
            || self.memory_loads_proven_equal(left, right)
    }

    /// Fact-transport equality, memoized by fact-set content identity.
    ///
    /// Order-fact matching asks this for every candidate fact of every
    /// decision, and the same term pairs recur across those scans, so the
    /// search is worth caching. The discipline is [`Self::decide`]'s: a
    /// `true` is evidence found in the facts and is always cacheable, while a
    /// `false` computed after an exact cycle cut or an observed verification
    /// limit is incomplete and is not. Memoized
    /// only under an enclosing id scope, so no call pays a fact-set hash.
    pub(in crate::kernel) fn bitvector_terms_equal_for_transport(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        if left == right {
            return true;
        }
        let memo_id = ambient_assumptions_memo_id(self);
        let memo_key = memo_id.map(|memo_id| (memo_id, left.clone(), right.clone()));
        if let Some(memo_key) = &memo_key
            && let Some(hit) =
                TRANSPORT_EQUAL_MEMO.with(|memo| memo.borrow().get(memo_key).copied())
        {
            return hit;
        }
        let epoch_before = INCOMPLETE_REASONING_EPOCH.with(Cell::get);
        let result = self.bitvector_terms_equal_for_transport_uncached(left, right);
        if let Some(memo_key) = memo_key
            && (result || INCOMPLETE_REASONING_EPOCH.with(Cell::get) == epoch_before)
        {
            TRANSPORT_EQUAL_MEMO.with(|memo| {
                let mut memo = memo.borrow_mut();
                if memo.len() >= DECIDE_MEMO_LIMIT {
                    memo.clear();
                }
                memo.insert(memo_key, result);
            });
        }
        result
    }

    fn bitvector_terms_equal_for_transport_uncached(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        // Transport compares int32 values, so wrapping equality from the
        // trusted graph is sufficient here. Broader proof reasoning remains
        // separate from this known-value query.
        if self.int32_values_known_equal(left, right)
            || self.bitvector_terms_proven_equal(left, right)
        {
            return true;
        }

        if let (Some((operator, left_a, left_b)), Some((other, right_a, right_b))) =
            (left.as_binary(), right.as_binary())
        {
            return operator == other
                && operator.is_bitvector32()
                && !matches!(
                    operator,
                    crate::kernel::BitvectorBinaryOp::UnsignedDivide
                        | crate::kernel::BitvectorBinaryOp::UnsignedRemainder
                )
                && self.bitvector_terms_equal_for_transport(left_a, right_a)
                && self.bitvector_terms_equal_for_transport(left_b, right_b);
        }
        match (left, right) {
            (Bitvector32Term::BitwiseNot(left), Bitvector32Term::BitwiseNot(right)) => {
                self.bitvector_terms_equal_for_transport(left, right)
            }
            _ => false,
        }
    }

    fn pointer_offset_terms_equal_for_transport(
        &self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> bool {
        if left == right {
            return true;
        }

        match (left, right) {
            (
                PointerOffsetTerm::Int32Scaled {
                    value: left,
                    byte_width: left_width,
                },
                PointerOffsetTerm::Int32Scaled {
                    value: right,
                    byte_width: right_width,
                },
            ) => left_width == right_width && self.bitvector_terms_equal_for_transport(left, right),
            (PointerOffsetTerm::Add(left_a, left_b), PointerOffsetTerm::Add(right_a, right_b)) => {
                self.pointer_offset_terms_equal_for_transport(left_a, right_a)
                    && self.pointer_offset_terms_equal_for_transport(left_b, right_b)
                    || self.pointer_offset_terms_equal_for_transport(left_a, right_b)
                        && self.pointer_offset_terms_equal_for_transport(left_b, right_a)
            }
            _ => false,
        }
    }

    fn pointer_offset_terms_snapshot_equivalent(
        &self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> bool {
        if left == right {
            return true;
        }
        match (left, right) {
            (
                PointerOffsetTerm::Int32Scaled {
                    value: left,
                    byte_width: left_width,
                },
                PointerOffsetTerm::Int32Scaled {
                    value: right,
                    byte_width: right_width,
                },
            ) => left_width == right_width && self.bitvector_terms_snapshot_equivalent(left, right),
            (PointerOffsetTerm::Add(left_a, left_b), PointerOffsetTerm::Add(right_a, right_b)) => {
                self.pointer_offset_terms_snapshot_equivalent(left_a, right_a)
                    && self.pointer_offset_terms_snapshot_equivalent(left_b, right_b)
                    || self.pointer_offset_terms_snapshot_equivalent(left_a, right_b)
                        && self.pointer_offset_terms_snapshot_equivalent(left_b, right_a)
            }
            _ => false,
        }
    }

    pub(in crate::kernel) fn has_pointer_offset_snapshot_fact(
        &self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> bool {
        // Keep this deliberately structural and one-hop. Callers use it only
        // to move an already-certified address equality between framed memory
        // snapshots, never to synthesize a new alias relationship.
        self.condition_facts.iter().any(|(condition, value)| {
            if !*value {
                return false;
            }
            let ConditionTerm::PointerOffsetEqual(fact_left, fact_right) = condition else {
                return false;
            };
            self.pointer_offset_terms_snapshot_equivalent(fact_left, left)
                && self.pointer_offset_terms_snapshot_equivalent(fact_right, right)
                || self.pointer_offset_terms_snapshot_equivalent(fact_left, right)
                    && self.pointer_offset_terms_snapshot_equivalent(fact_right, left)
        })
    }

    pub(super) fn bitvector_terms_snapshot_equivalent(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        if left == right {
            return true;
        }
        match (left, right) {
            (Bitvector32Term::MemoryLoad(_, _, _), Bitvector32Term::MemoryLoad(_, _, _)) => {
                memory_load_terms_equal_for_fact_transport(left, right, self)
            }
            (Bitvector32Term::Add(left_a, left_b), Bitvector32Term::Add(right_a, right_b))
            | (
                Bitvector32Term::Subtract(left_a, left_b),
                Bitvector32Term::Subtract(right_a, right_b),
            )
            | (
                Bitvector32Term::Multiply(left_a, left_b),
                Bitvector32Term::Multiply(right_a, right_b),
            ) => {
                self.bitvector_terms_snapshot_equivalent(left_a, right_a)
                    && self.bitvector_terms_snapshot_equivalent(left_b, right_b)
            }
            _ => false,
        }
    }

    pub(in crate::kernel) fn bitvector_if_terms_proven_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let (
            Bitvector32Term::If {
                condition: left_condition,
                then_term: left_then,
                else_term: left_else,
            },
            Bitvector32Term::If {
                condition: right_condition,
                then_term: right_then,
                else_term: right_else,
            },
        ) = (left, right)
        else {
            return false;
        };

        (left_condition == right_condition
            || self.condition_matches(left_condition, right_condition)
            || self.condition_matches(right_condition, left_condition))
            && self.bitvector_terms_proven_equal(left_then, right_then)
            && self.bitvector_terms_proven_equal(left_else, right_else)
    }

    pub(in crate::kernel) fn bitvector_add_terms_proven_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        if !matches!(left, Bitvector32Term::Add(_, _))
            && !matches!(right, Bitvector32Term::Add(_, _))
        {
            return false;
        }

        let mut left_terms = Vec::new();
        let mut left_constant = 0u32;
        collect_bitvector_add_terms(left, &mut left_terms, &mut left_constant);

        let mut right_terms = Vec::new();
        let mut right_constant = 0u32;
        collect_bitvector_add_terms(right, &mut right_terms, &mut right_constant);

        if left_constant != right_constant || left_terms.len() != right_terms.len() {
            return false;
        }

        for left_term in left_terms {
            let Some(index) = right_terms.iter().position(|right_term| {
                self.bitvector_addend_terms_proven_equal(&left_term, right_term)
            }) else {
                return false;
            };
            right_terms.remove(index);
        }

        right_terms.is_empty()
    }

    pub(in crate::kernel) fn bitvector_addend_terms_proven_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        left == right
            || self.bitvector_if_terms_proven_equal(left, right)
            || self.range_fold_terms_alpha_equivalent(left, right)
            || self.int32_values_known_equal(left, right)
            || self.memory_loads_proven_equal(left, right)
    }

    pub(in crate::kernel) fn count_fold_split_terms_proven_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        count_fold_split_matches(left, right, self) || count_fold_split_matches(right, left, self)
    }

    pub(in crate::kernel) fn range_fold_terms_alpha_equivalent(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        range_fold_terms_alpha_equivalent(left, right, self)
    }

    pub(in crate::kernel) fn proves_without_prop_facts(&self, proposition: &Proposition) -> bool {
        if solve_builtin_prop(proposition) {
            return true;
        }

        let directly_proven = match proposition {
            Proposition::ConditionIs(condition, value) => self.decide(condition) == Some(*value),
            Proposition::And(left, right) => {
                self.proves_without_prop_facts(left) && self.proves_without_prop_facts(right)
            }
            Proposition::Or(left, right) => {
                self.proves_without_prop_facts(left) || self.proves_without_prop_facts(right)
            }
            Proposition::Not(body) => match body.as_ref() {
                Proposition::ConditionIs(condition, value) => {
                    self.decide(condition) == Some(!*value)
                }
                _ => false,
            },
            _ => false,
        };
        if directly_proven {
            return true;
        }

        // Inconsistency proves every proposition. It is an indexed read,
        // after the direct evidence.
        self.is_inconsistent()
    }

    pub(crate) fn is_inconsistent(&self) -> bool {
        // The closure can discover a constant conflict on demand, after its
        // facts were filed.
        if self.equality_graph.has_scalar_constant_conflict()
            || !self.algebraic_constructor_conflicts.is_empty()
        {
            return true;
        }
        self.contradictions
            .index(|| {
                self.condition_facts
                    .iter()
                    .map(|(condition, value)| (condition, *value))
                    .collect()
            })
            .is_contradictory()
    }

    /// Every contradiction rule applied to all of this context's facts at
    /// once: the reference the contradiction index is tested against
    /// (`contradictions.rs`).
    #[cfg(test)]
    pub(super) fn reference_inconsistency_scan(&self) -> bool {
        if !self.algebraic_constructor_conflicts.is_empty() {
            return true;
        }
        let fact_scan_timing = crate::instrumentation::OperationTiming::new(
            "kernel",
            "context inconsistency",
            "context inconsistency: fact scan and exact indexes",
        );
        let mut order_facts = Vec::new();
        let mut equal_facts = Vec::new();
        let mut disequal_facts = Vec::new();
        let mut exact_equal_pairs = BTreeSet::new();
        let mut exact_disequal_pairs = BTreeSet::new();
        let mut exact_order_pairs = BTreeMap::<(Bitvector32Term, Bitvector32Term), bool>::new();
        let mut condition_polarities = BTreeMap::new();
        for (condition, value) in self.condition_facts.iter() {
            crate::instrumentation::record_deterministic_work(1);
            let key = canonical_contradiction_condition(condition);
            // Canonicalization folds a comparison of constants to its value.
            if matches!(&key, ConditionTerm::Constant(actual) if actual != value) {
                return true;
            }
            if condition_polarities
                .insert(key, *value)
                .is_some_and(|prior| prior != *value)
            {
                return true;
            }
            // Full pointer equality entails address equality, while its
            // negation makes no claim about addresses.
            if let ConditionTerm::PointerValueEqual(left, right) = condition
                && *value
            {
                let address =
                    ConditionTerm::pointer_equal(left.pointer().clone(), right.pointer().clone());
                if condition_polarities.insert(canonical_contradiction_condition(&address), true)
                    == Some(false)
                {
                    return true;
                }
            }
            match (condition, value) {
                (ConditionTerm::Constant(actual), expected) if actual != expected => return true,
                (
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left,
                        right,
                    },
                    true,
                ) => {
                    equal_facts.push((left.as_ref().clone(), right.as_ref().clone()));
                    let pair = if left <= right {
                        (left.as_ref().clone(), right.as_ref().clone())
                    } else {
                        (right.as_ref().clone(), left.as_ref().clone())
                    };
                    exact_equal_pairs.insert(pair);
                }
                (
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left,
                        right,
                    },
                    false,
                ) => {
                    disequal_facts.push((left.as_ref().clone(), right.as_ref().clone()));
                    let pair = if left <= right {
                        (left.as_ref().clone(), right.as_ref().clone())
                    } else {
                        (right.as_ref().clone(), left.as_ref().clone())
                    };
                    exact_disequal_pairs.insert(pair);
                }
                _ => {
                    if let Some(order_fact) = condition_as_order_fact(condition, *value) {
                        let pair = (order_fact.0.clone(), order_fact.1.clone());
                        exact_order_pairs
                            .entry(pair)
                            .and_modify(|strict| *strict |= order_fact.2)
                            .or_insert(order_fact.2);
                        order_facts.push(order_fact);
                    }
                }
            }
        }
        drop(fact_scan_timing);

        let exact_timing = crate::instrumentation::OperationTiming::new(
            "kernel",
            "context inconsistency",
            "context inconsistency: exact conflicts",
        );
        if exact_equal_pairs
            .iter()
            .any(|pair| exact_disequal_pairs.contains(pair))
        {
            return true;
        }
        if exact_order_pairs.iter().any(|((left, right), strict)| {
            (left == right && *strict)
                || exact_order_pairs
                    .get(&(right.clone(), left.clone()))
                    .is_some_and(|reverse_strict| *strict || *reverse_strict)
                || (*strict
                    && exact_equal_pairs.contains(&if left <= right {
                        (left.clone(), right.clone())
                    } else {
                        (right.clone(), left.clone())
                    }))
        }) {
            return true;
        }
        drop(exact_timing);

        let derived_pair_timing = crate::instrumentation::OperationTiming::new(
            "kernel",
            "context inconsistency",
            "context inconsistency: derived pair conflicts",
        );
        let equality_conflict_timing = crate::instrumentation::OperationTiming::new(
            "kernel",
            "context inconsistency",
            "context inconsistency: derived equality conflicts",
        );
        for (equal_left, equal_right) in &equal_facts {
            crate::instrumentation::record_deterministic_work(1);
            if disequal_facts
                .iter()
                .any(|(disequal_left, disequal_right)| {
                    crate::instrumentation::record_deterministic_work(1);
                    (equal_left == disequal_left && equal_right == disequal_right)
                        || (equal_left == disequal_right && equal_right == disequal_left)
                })
            {
                return true;
            }
        }
        drop(equality_conflict_timing);

        let class_timing = crate::instrumentation::OperationTiming::new(
            "kernel",
            "context inconsistency",
            "context inconsistency: order equality classes",
        );

        /// Union-find over component labels, so canonical-form identities can
        /// merge equality-graph components without rebuilding them.
        struct ClassMerge(Vec<usize>);
        impl ClassMerge {
            fn find(&mut self, id: usize) -> usize {
                while self.0.len() <= id {
                    let next = self.0.len();
                    self.0.push(next);
                }
                let mut id = id;
                while self.0[id] != id {
                    self.0[id] = self.0[self.0[id]];
                    id = self.0[id];
                }
                id
            }
            fn union(&mut self, left: usize, right: usize) {
                let left = self.find(left);
                let right = self.find(right);
                if left != right {
                    self.0[right] = left;
                }
            }
        }

        /// The component label of one key, walking its equality-graph
        /// component on first use. A key with no equality fact becomes its
        /// own singleton, and a component no relevant term touches is never
        /// walked.
        fn key_component(
            key: Bitvector32Term,
            equality_graph: &crate::kernel::equality_graph::EqualityGraph,
            class_of_key: &mut BTreeMap<Bitvector32Term, usize>,
            next_class: &mut usize,
        ) -> usize {
            if let Some(class) = class_of_key.get(&key) {
                return *class;
            }
            let class = *next_class;
            *next_class += 1;
            let members = equality_graph.scalar_evidence_class(&key);
            for term in std::iter::once(key).chain(members) {
                crate::instrumentation::record_deterministic_work(1);
                class_of_key.insert(term, class);
            }
            class
        }

        let equality_index = &self.equality_graph;
        let mut class_of_key = BTreeMap::<Bitvector32Term, usize>::new();
        let mut next_class = 0usize;
        let mut merged = ClassMerge(Vec::new());
        let mut registered = BTreeMap::<Bitvector32Term, usize>::new();
        {
            let order_endpoints = order_facts
                .iter()
                .flat_map(|(left, right, _)| [left, right]);
            let equal_sides = equal_facts.iter().flat_map(|(left, right)| [left, right]);
            for term in order_endpoints.chain(equal_sides) {
                if registered.contains_key(term) {
                    continue;
                }
                crate::instrumentation::record_deterministic_work(1);
                let bucket_key = order_endpoint_key(term);
                let graph_component = key_component(
                    equality_graph_term_key(term),
                    equality_index,
                    &mut class_of_key,
                    &mut next_class,
                );
                let bucket_component = key_component(
                    bucket_key,
                    equality_index,
                    &mut class_of_key,
                    &mut next_class,
                );
                merged.union(graph_component, bucket_component);
                registered.insert(term.clone(), bucket_component);
            }
        }
        let final_class = registered
            .iter()
            .map(|(term, component)| (term.clone(), merged.find(*component)))
            .collect::<BTreeMap<_, _>>();
        let order_classes = order_facts
            .iter()
            .map(|(left, right, _)| (final_class[left], final_class[right]))
            .collect::<Vec<_>>();
        drop(class_timing);

        let order_conflict_timing = crate::instrumentation::OperationTiming::new(
            "kernel",
            "context inconsistency",
            "context inconsistency: derived order conflicts",
        );
        // A strict edge inside one class contradicts the equality chain that
        // built the class, and a reverse edge between two classes contradicts
        // this one when either edge is strict. Both are map lookups, so a
        // consistent context costs one pass rather than an all-pairs scan.
        let mut class_order = BTreeMap::<(usize, usize), bool>::new();
        for ((left_class, right_class), (_, _, strict)) in
            order_classes.iter().zip(order_facts.iter())
        {
            crate::instrumentation::record_deterministic_work(1);
            if *strict && left_class == right_class {
                return true;
            }
            if class_order
                .get(&(*right_class, *left_class))
                .is_some_and(|reverse_strict| *strict || *reverse_strict)
            {
                return true;
            }
            class_order
                .entry((*left_class, *right_class))
                .and_modify(|existing| *existing |= *strict)
                .or_insert(*strict);
        }

        drop(order_conflict_timing);
        drop(derived_pair_timing);

        if crate::instrumentation::measure_operation(
            "kernel",
            "context inconsistency",
            "context inconsistency: finite range",
            || finite_integer_range_exhausted(&order_facts, &equal_facts, &disequal_facts),
        ) {
            return true;
        }

        false
    }
}

/// Flatten one additive form without using the Rust call stack.
pub(super) fn collect_order_index_add_terms(
    term: &Bitvector32Term,
    terms: &mut Vec<Bitvector32Term>,
    constant: &mut u32,
) {
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match term {
            Bitvector32Term::Add(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            Bitvector32Term::Constant(value) => {
                *constant = constant.wrapping_add(*value);
            }
            term => terms.push(term.clone()),
        }
    }
}

/// The contradiction index's key for one order endpoint: constants fold,
/// addends sort, a load keeps its context-free form, and a sum that
/// collapses to one addend becomes that addend.
///
/// Each rewrite is a context-free kernel equality (bitvector addition, or
/// context-free equality for loads), so terms sharing a key are provably
/// equal in every context. It is an index key rather than global canonical
/// form. The explicit worklist traverses every input node without a depth
/// cutoff.
pub(super) fn order_endpoint_key(term: &Bitvector32Term) -> Bitvector32Term {
    enum Task {
        Visit(Bitvector32Term),
        RebuildAdd { count: usize, constant: u32 },
        RebuildIf(ConditionTerm),
    }

    let mut tasks = vec![Task::Visit(term.clone())];
    let mut results = Vec::<Bitvector32Term>::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(term) => {
                crate::instrumentation::record_deterministic_work(1);
                match term {
                    term @ Bitvector32Term::MemoryLoad(_, _, _) => {
                        results.push(equality_graph_term_key(&term));
                    }
                    term @ Bitvector32Term::Add(_, _) => {
                        let mut raw = Vec::new();
                        let mut constant = 0u32;
                        collect_order_index_add_terms(&term, &mut raw, &mut constant);
                        tasks.push(Task::RebuildAdd {
                            count: raw.len(),
                            constant,
                        });
                        tasks.extend(raw.into_iter().rev().map(Task::Visit));
                    }
                    Bitvector32Term::If {
                        condition,
                        then_term,
                        else_term,
                    } => {
                        tasks.push(Task::RebuildIf(*condition));
                        tasks.push(Task::Visit(*else_term));
                        tasks.push(Task::Visit(*then_term));
                    }
                    term => results.push(term),
                }
            }
            Task::RebuildAdd {
                count,
                mut constant,
            } => {
                let split = results.len().checked_sub(count).expect("visited addends");
                let normalized = results.split_off(split);
                let mut addends = Vec::new();
                for addend in normalized {
                    collect_order_index_add_terms(&addend, &mut addends, &mut constant);
                }
                addends.sort();
                let mut written = if constant == 0 && !addends.is_empty() {
                    None
                } else {
                    Some(Bitvector32Term::Constant(constant))
                };
                for addend in addends.into_iter().rev() {
                    written = Some(match written {
                        Some(rest) => Bitvector32Term::add(addend, rest),
                        None => addend,
                    });
                }
                results.push(written.expect("an add form always has at least one part"));
            }
            Task::RebuildIf(condition) => {
                let else_term = results.pop().expect("visited else endpoint");
                let then_term = results.pop().expect("visited then endpoint");
                results.push(Bitvector32Term::If {
                    condition: Box::new(condition),
                    then_term: Box::new(then_term),
                    else_term: Box::new(else_term),
                });
            }
        }
    }
    let result = results
        .pop()
        .expect("endpoint normalization produces one key");
    debug_assert!(results.is_empty());
    result
}

#[cfg(test)]
mod constant_prefix_certificate_tests {
    use super::*;

    #[test]
    fn order_path_checks_normalized_constant_prefix_and_live_premise() {
        let upper = Bitvector32Term::Variable(Variable(999_481));
        let premise = ConditionTerm::signed_less_equal(2u32.into(), upper.clone());
        let context = PureFactContext::new().assume_condition(premise.clone(), true);
        let path = context
            .exact_signed_order_path_evidence(&1u32.into(), &upper, true)
            .unwrap();
        assert_eq!(path[0].lower, Bitvector32Term::Constant(2));
        assert!(context.checks_exact_signed_order_path(&path, &1u32.into(), &upper, true));
        assert!(context.checks_exact_signed_order_path(&path, &2u32.into(), &upper, false));
        assert!(!context.checks_exact_signed_order_path(&path, &2u32.into(), &upper, true));
        assert!(!context.checks_exact_signed_order_path(&path, &3u32.into(), &upper, false));
        assert!(!context.checks_exact_signed_order_path(
            &path,
            &Bitvector32Term::Variable(Variable(999_482)),
            &upper,
            false,
        ));
        let withdrawn = context.without_exact_fact(&Proposition::ConditionIs(premise, true));
        assert!(!withdrawn.checks_exact_signed_order_path(&path, &1u32.into(), &upper, true));
    }
}

/// The atomic derivation memo's key. The derivation matches order-path
/// terms through memory derivations only while the extended DAG bridging is
/// active (`order_paths.rs`), and the DAG modes are scoped so that answers
/// outside them stay unchanged, so an answer is reused only in the modes it
/// was computed in.
fn atomic_derivation_memo_key(premises_id: u64, for_simp: bool) -> (u64, bool, bool, bool) {
    (
        premises_id,
        for_simp,
        crate::kernel::api::extended_dag_bridging_active(),
        crate::kernel::api::explicit_dag_check_active(),
    )
}

/// Whether an atomic derivation of `proposition` is memoized for these
/// premises in the current DAG modes.
#[cfg(test)]
pub(crate) fn atomic_derivation_is_memoized(
    premises_id: u64,
    proposition: &Proposition,
    for_simp: bool,
) -> bool {
    ATOMIC_DERIVATION_MEMO.with(|memo| {
        memo.borrow()
            .get(&atomic_derivation_memo_key(premises_id, for_simp))
            .is_some_and(|entries| entries.contains_key(proposition))
    })
}

#[cfg(test)]
mod guided_condition_instantiation_tests {
    use super::*;

    fn variable(id: u64) -> Bitvector32Term {
        Bitvector32Term::Variable(Variable(id))
    }

    fn array_read(index: Bitvector32Term, kind: LoadKind) -> Bitvector32Term {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(CMemory::new()),
            Box::new(Pointer {
                block: "quantified-cells".into(),
                offset: PointerOffsetTerm::scale_int32(index, 4),
            }),
            kind,
        )
    }

    fn body() -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::equal(array_read(variable(998_100), LoadKind::Bits32), 0u32.into()),
            true,
        )
    }

    #[test]
    fn guided_condition_instantiation_keeps_matching_cell_index() {
        let _session = crate::kernel::VerificationSession::enter();
        let target =
            ConditionTerm::equal(array_read(variable(998_101), LoadKind::Bits32), 0u32.into());
        assert_eq!(
            PureFactContext::guided_forall_condition_candidates(
                Variable(998_100),
                &body(),
                &target
            ),
            BTreeSet::from([variable(998_101)])
        );
        let wrong_kind =
            ConditionTerm::equal(array_read(variable(998_101), LoadKind::UInt8), 0u32.into());
        assert!(
            PureFactContext::guided_forall_condition_candidates(
                Variable(998_100),
                &body(),
                &wrong_kind
            )
            .is_empty()
        );
    }

    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/assumptions/proposition_reasoning/guided_condition_instantiation_tests.rs"
        );
    }
}

#[cfg(test)]
mod annotated_alignment_conflict_tests {
    use super::*;

    #[test]
    fn address_class_annotations_do_not_hide_opposite_alignment_facts() {
        let pointer = Pointer::symbolic(Variable(970_001));
        let class = crate::kernel::effective_type::CAccessClass::Struct(
            crate::kernel::effective_type::CStructClass::opaque("node"),
        );
        let aligned =
            Proposition::ConditionIs(ConditionTerm::pointer_aligned(pointer.clone(), 8), true);
        let masked_address = Bitvector32Term::uint64_bitwise_and(
            Bitvector32Term::object_pointer_address(pointer, Some(class)),
            Bitvector32Term::UInt64Constant(7),
        );
        let zero = Bitvector32Term::UInt64Constant(0);
        assert_eq!(
            aligned,
            Proposition::ConditionIs(
                ConditionTerm::uint64_equal(masked_address.clone(), zero.clone()),
                true
            ),
        );
        // An address's class is not part of its identity, so the classed
        // spelling is the same term as the bare one and cannot hide a fact.
        assert_eq!(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: Box::new(masked_address.clone()),
                right: Box::new(zero.clone())
            },
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: Box::new(Bitvector32Term::uint64_bitwise_and(
                    Bitvector32Term::object_pointer_address(
                        Pointer::symbolic(Variable(970_001)),
                        None,
                    ),
                    Bitvector32Term::UInt64Constant(7),
                )),
                right: Box::new(zero.clone())
            },
        );
        // The context's same-key insertion replaces its prior value. Admit
        // a distinct spelling (operands swapped) to exercise congruence
        // conflict handling; the factory's canonical spelling was checked
        // above.
        let not_aligned = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: Box::new(zero),
                right: Box::new(masked_address),
            },
            false,
        );
        let base = PureFactContext::new().assume_proposition(aligned.clone());
        let branch = base.clone().assume_proposition(not_aligned.clone());
        assert!(branch.is_inconsistent());
        assert!(!base.is_inconsistent());
        assert!(!branch.without_exact_fact(&aligned).is_inconsistent());
        assert!(!branch.without_exact_fact(&not_aligned).is_inconsistent());
    }
}

#[cfg(test)]
mod congruent_condition_conflict_tests {
    use super::*;

    #[test]
    fn equal_address_alignment_conflicts_follow_merges_and_withdrawal() {
        let p = Pointer::symbolic(Variable(971_001));
        let q = Pointer::symbolic(Variable(971_002));
        let equality =
            Proposition::ConditionIs(ConditionTerm::pointer_equal(p.clone(), q.clone()), true);
        let aligned = Proposition::ConditionIs(ConditionTerm::pointer_aligned(p, 8), true);
        let not_aligned = Proposition::ConditionIs(ConditionTerm::pointer_aligned(q, 8), false);
        for facts in [
            [equality.clone(), aligned.clone(), not_aligned.clone()],
            [aligned.clone(), not_aligned.clone(), equality.clone()],
            [not_aligned.clone(), equality.clone(), aligned.clone()],
        ] {
            let mut context = PureFactContext::new();
            for fact in facts {
                context = context.assume_proposition(fact);
            }
            assert!(context.is_inconsistent());
            for fact in [&equality, &aligned, &not_aligned] {
                assert!(!context.without_exact_fact(fact).is_inconsistent());
            }
        }
        let parent = PureFactContext::new()
            .assume_proposition(aligned)
            .assume_proposition(not_aligned);
        assert!(!parent.is_inconsistent());
        assert!(
            parent
                .clone()
                .assume_proposition(equality)
                .is_inconsistent()
        );
        assert!(!parent.is_inconsistent());
    }
    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/assumptions/proposition_reasoning/congruent_condition_conflict_tests.rs"
        );
    }
}

#[cfg(test)]
mod comparison_operand_order_tests {
    use super::*;

    fn getter(size: u64) -> Bitvector32Term {
        Bitvector32Term::ClickFunctionApplication {
            name: "selected_size".into(),
            arguments: (0..size)
                .map(|index| {
                    PureFunctionArgument::Value(CValue::typed_pointer(
                        Pointer::symbolic(Variable(9_992_000 + size * 1000 + index)),
                        CType::Int32Pointer,
                    ))
                })
                .collect(),
        }
    }

    #[test]
    fn comparison_matching_keeps_equal_bound_aliases_and_mirrored_orders() {
        let _session = crate::kernel::VerificationSession::enter();
        let value = getter(4);
        let x = Bitvector32Term::Variable(Variable(9_991_001));
        let bound = Bitvector32Term::Variable(Variable(9_991_002));
        let limit = Bitvector32Term::Constant(2147483646);
        let value_alias =
            Proposition::ConditionIs(ConditionTerm::equal(value.clone(), x.clone()), true);
        let bound_alias =
            Proposition::ConditionIs(ConditionTerm::equal(bound.clone(), limit.clone()), true);
        let fact = ConditionTerm::signed_less_equal(value, limit);
        let parent = PureFactContext::new().assume_condition(fact.clone(), true);
        let child = parent
            .clone()
            .assume_proposition(value_alias.clone())
            .assume_proposition(bound_alias.clone());
        for goal in [
            ConditionTerm::signed_less_equal(x.clone(), bound.clone()),
            ConditionTerm::signed_greater_equal(bound.clone(), x.clone()),
        ] {
            assert!(child.condition_matches(&fact, &goal));
            assert!(!parent.condition_matches(&fact, &goal));
            assert!(
                !child
                    .without_exact_fact(&value_alias)
                    .condition_matches(&fact, &goal)
            );
            assert!(
                !child
                    .without_exact_fact(&bound_alias)
                    .condition_matches(&fact, &goal)
            );
        }
    }

    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/assumptions/proposition_reasoning/comparison_operand_order_tests.rs"
        );
    }
}
