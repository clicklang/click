//! Checked equality substitution. Surface syntax is never evidence for a rewrite.

use super::fact_reasoning::exactly_available_fact;
use super::{ProofFacts, PropositionObligation, PropositionSource};
use crate::kernel::*;
use std::collections::BTreeSet;

/// A checked goal refinement and its path-local load-transport evidence.
/// Only this module can construct or change its semantic result.
pub(crate) struct CheckedEqualityRewrite {
    proposition: Proposition,
    facts: ProofFacts,
}

impl CheckedEqualityRewrite {
    pub(crate) fn proposition(&self) -> &Proposition {
        &self.proposition
    }

    /// A proposed surface spelling may use different load names. Accept it
    /// only through the kernel's checked, corresponding-leaf transport rule.
    pub(crate) fn try_present_as(&mut self, proposed: &Proposition) -> bool {
        if proposed == &self.proposition {
            return true;
        }
        // Surface lowering folds constant Integer expressions while an
        // exact substitution can leave their arithmetic structure intact.
        // Accept only the same normalized claim used by the checked Integer
        // certificate rules; this compares the selected propositions alone
        // and neither imports ambient facts nor transports different reads.
        if let (Some(original), Some(candidate)) = (
            super::integer_arithmetic::integer_affine_claim(&self.proposition),
            super::integer_arithmetic::integer_affine_claim(proposed),
        ) && original == candidate
        {
            self.proposition = proposed.clone();
            return true;
        }
        let Some(facts) = self
            .facts
            .with_checked_rewritten_loads(&self.proposition, proposed)
        else {
            return false;
        };
        self.facts = facts;
        self.proposition = proposed.clone();
        true
    }

    pub(crate) fn into_obligation<P, O>(
        self,
        presentation: P,
        outcome: Option<O>,
    ) -> (PropositionObligation<P, O>, ProofFacts) {
        let obligation = match outcome {
            Some(outcome) => {
                PropositionObligation::at_outcome(self.proposition, presentation, outcome)
            }
            None => PropositionObligation::new(self.proposition, presentation),
        };
        (obligation, self.facts)
    }
}

impl ProofFacts {
    /// Check one explicitly cited equality against the persistent premise
    /// index, then compute the exact substitution. This path never scans or
    /// rebuilds the ambient premise context. Goal lowering/unfolding precedes
    /// this rule; the returned obligation contains only the checked result.
    pub(crate) fn check_equality_rewrite(
        &self,
        goal: &Proposition,
        equality: &Proposition,
    ) -> Result<CheckedEqualityRewrite, String> {
        let admitted = equality_is_vacuous(equality)
            || self.materialization_available(equality)
            || reverse_equality(equality)
                .is_some_and(|reverse| self.materialization_available(&reverse));
        if !admitted {
            return Err(
                "`rewrite` requires its equality to be an exact available fact".to_string(),
            );
        }
        match rewrite_with_admitted_equality(goal, equality) {
            Ok(proposition) => Ok(CheckedEqualityRewrite {
                proposition,
                facts: self.clone(),
            }),
            Err(original_error) => {
                // Compare only the cited expression with the two operands of
                // this atomic goal. Corresponding operators stay exact; the
                // shared transport checker validates any changed read leaves.
                let (from, to, wide) = match equality {
                    Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(a, b), true) => {
                        (a, b, false)
                    }
                    Proposition::ConditionIs(ConditionTerm::Bitvector64Equal(a, b), true) => {
                        (a, b, true)
                    }
                    _ => return Err(original_error),
                };
                let (left, right) = match goal {
                    Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(a, b), _) if !wide => {
                        (a, b)
                    }
                    Proposition::ConditionIs(ConditionTerm::Bitvector64Equal(a, b), _) if wide => {
                        (a, b)
                    }
                    _ => return Err(original_error),
                };
                for selected in [left, right] {
                    if selected == from {
                        continue;
                    }
                    let condition = if wide {
                        ConditionTerm::Bitvector64Equal(selected.clone(), to.clone())
                    } else {
                        ConditionTerm::equal(selected.as_ref().clone(), to.as_ref().clone())
                    };
                    let adapted = Proposition::ConditionIs(condition, true);
                    let Some(facts) = self.with_checked_rewritten_loads(equality, &adapted) else {
                        continue;
                    };
                    if let Ok(proposition) = rewrite_with_admitted_equality(goal, &adapted) {
                        return Ok(CheckedEqualityRewrite { proposition, facts });
                    }
                }
                Err(original_error)
            }
        }
    }
}

pub(crate) fn reverse_equality(equality: &Proposition) -> Option<Proposition> {
    let reversed = match equality {
        Proposition::Equal(Term::Algebraic(a), Term::Algebraic(b)) => {
            return Some(Proposition::Equal(
                Term::Algebraic(b.clone()),
                Term::Algebraic(a.clone()),
            ));
        }
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(a, b), true) => {
            ConditionTerm::Bitvector32Equal(b.clone(), a.clone())
        }
        Proposition::ConditionIs(ConditionTerm::Bitvector64Equal(a, b), true) => {
            ConditionTerm::Bitvector64Equal(b.clone(), a.clone())
        }
        Proposition::ConditionIs(ConditionTerm::IntegerEqual(a, b), true) => {
            ConditionTerm::IntegerEqual(b.clone(), a.clone())
        }
        Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(a, b), true) => {
            ConditionTerm::PointerOffsetEqual(b.clone(), a.clone())
        }
        Proposition::ConditionIs(ConditionTerm::PointerValueEqual(a, b), true) => {
            ConditionTerm::PointerValueEqual(b.clone(), a.clone())
        }
        Proposition::ConditionIs(ConditionTerm::PointerEqual(a, b), true) => {
            ConditionTerm::PointerEqual(b.clone(), a.clone())
        }
        _ => return None,
    };
    Some(Proposition::ConditionIs(reversed, true))
}

// Equality substitution cares about lexical variables, not the contents of
// immutable snapshots. The shared checked collector also sees variables in
// pure-function arguments and registered load addresses.
fn rewrite_equality_variables(equality: &Proposition) -> Result<BTreeSet<Variable>, String> {
    let mut collector =
        crate::kernel::proof::term_rewrite::IntegerSubstitutionVariableCollector::checked();
    collector.collect(equality);
    if collector.exhausted() {
        return Err(
            "`rewrite` exhausted its work budget while checking binder capture".to_string(),
        );
    }
    let mut variables = BTreeSet::new();
    collector.extend_into(&mut variables);
    Ok(variables)
}

/// Candidate construction for smart planning over an explicit premise slice.
/// The result has no proof authority; certificate checking uses the indexed
/// `ProofFacts::check_equality_rewrite` rule instead.
pub(crate) fn rewrite_proposition_by_exact_equality(
    goal: &Proposition,
    equality: &Proposition,
    available: &[Proposition],
) -> Result<Proposition, String> {
    let bridging_assumptions = std::cell::OnceCell::new();
    let is_available = |fact: &Proposition| {
        available.contains(fact)
            || exactly_available_fact(fact, available).is_some()
            || super::fact_reasoning::premise_bridged_by_load_variable_chain_with_origins(
                fact,
                available,
                bridging_assumptions.get_or_init(|| available.pure_context()),
            )
    };
    if !equality_is_vacuous(equality)
        && !is_available(equality)
        && !reverse_equality(equality)
            .as_ref()
            .is_some_and(is_available)
    {
        return Err("`rewrite` requires its equality to be an exact available fact".to_string());
    }
    rewrite_with_admitted_equality(goal, equality)
}

/// Whether `equality` replaces some occurrence in `goal`. Smart planning
/// uses it to skip a rewrite that cannot apply; it has no proof authority,
/// and the checked `rewrite` step decides.
pub(crate) fn equality_rewrite_applies(goal: &Proposition, equality: &Proposition) -> bool {
    !equality_is_vacuous(equality)
        && rewrite_with_admitted_equality(goal, equality).is_ok_and(|rewritten| rewritten != *goal)
}

fn rewrite_with_admitted_equality(
    goal: &Proposition,
    equality: &Proposition,
) -> Result<Proposition, String> {
    if equality_is_vacuous(equality) {
        return Ok(goal.clone());
    }
    let byte_equality = signed_byte_equality_as_byte_equality(equality);
    let equality = byte_equality.as_ref().unwrap_or(equality);
    enum RewriteTask<'a> {
        Visit(&'a Proposition),
        BuildAnd,
        BuildOr,
        BuildNot,
        BuildImplies,
        BuildForAll {
            var: Variable,
            sort: Sort,
        },
        BuildExists {
            name: String,
            var: Variable,
            sort: Sort,
        },
    }

    let mut tasks = vec![RewriteTask::Visit(goal)];
    let mut results: Vec<(Proposition, bool)> = Vec::new();
    let equality_variables = std::cell::OnceCell::new();
    let mut blocked_by_binder = false;
    while let Some(task) = tasks.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match task {
            RewriteTask::Visit(proposition) => match proposition {
                Proposition::And(left, right) => {
                    tasks.push(RewriteTask::BuildAnd);
                    tasks.push(RewriteTask::Visit(right));
                    tasks.push(RewriteTask::Visit(left));
                }
                Proposition::Or(left, right) => {
                    tasks.push(RewriteTask::BuildOr);
                    tasks.push(RewriteTask::Visit(right));
                    tasks.push(RewriteTask::Visit(left));
                }
                Proposition::Not(body) => {
                    tasks.push(RewriteTask::BuildNot);
                    tasks.push(RewriteTask::Visit(body));
                }
                Proposition::Implies(antecedent, consequent) => {
                    tasks.push(RewriteTask::BuildImplies);
                    tasks.push(RewriteTask::Visit(consequent));
                    tasks.push(RewriteTask::Visit(antecedent));
                }
                Proposition::ForAll { var, sort, body } => {
                    if equality_variables
                        .get_or_init(|| rewrite_equality_variables(equality))
                        .as_ref()
                        .map_err(Clone::clone)?
                        .contains(var)
                    {
                        // Substitution below this binder could replace a bound
                        // occurrence or capture a variable in the replacement.
                        blocked_by_binder = true;
                        results.push((proposition.clone(), false));
                    } else {
                        tasks.push(RewriteTask::BuildForAll {
                            var: *var,
                            sort: sort.clone(),
                        });
                        tasks.push(RewriteTask::Visit(body));
                    }
                }
                Proposition::Exists {
                    name,
                    var,
                    sort,
                    body,
                } => {
                    if equality_variables
                        .get_or_init(|| rewrite_equality_variables(equality))
                        .as_ref()
                        .map_err(Clone::clone)?
                        .contains(var)
                    {
                        blocked_by_binder = true;
                        results.push((proposition.clone(), false));
                    } else {
                        tasks.push(RewriteTask::BuildExists {
                            name: name.clone(),
                            var: *var,
                            sort: sort.clone(),
                        });
                        tasks.push(RewriteTask::Visit(body));
                    }
                }
                atomic => match rewrite_atomic_proposition_by_exact_equality(atomic, equality) {
                    Ok(rewritten) => results.push((rewritten, true)),
                    Err(AtomicRewriteRefusal::Absent(_)) => {
                        results.push((atomic.clone(), false));
                    }
                    Err(refusal) => return Err(refusal.into()),
                },
            },
            RewriteTask::BuildAnd | RewriteTask::BuildOr | RewriteTask::BuildImplies => {
                let (right, right_changed) = results.pop().expect("right rewrite result");
                let (left, left_changed) = results.pop().expect("left rewrite result");
                let rewritten = match task {
                    RewriteTask::BuildAnd => Proposition::And(Box::new(left), Box::new(right)),
                    RewriteTask::BuildOr => Proposition::Or(Box::new(left), Box::new(right)),
                    RewriteTask::BuildImplies => {
                        Proposition::Implies(Box::new(left), Box::new(right))
                    }
                    _ => unreachable!(),
                };
                results.push((rewritten, left_changed || right_changed));
            }
            RewriteTask::BuildNot => {
                let (body, changed) = results.pop().expect("negation rewrite result");
                results.push((Proposition::Not(Box::new(body)), changed));
            }
            RewriteTask::BuildForAll { var, sort } => {
                let (body, changed) = results.pop().expect("universal rewrite result");
                results.push((
                    Proposition::ForAll {
                        var,
                        sort,
                        body: Box::new(body),
                    },
                    changed,
                ));
            }
            RewriteTask::BuildExists { name, var, sort } => {
                let (body, changed) = results.pop().expect("existential rewrite result");
                results.push((
                    Proposition::Exists {
                        name,
                        var,
                        sort,
                        body: Box::new(body),
                    },
                    changed,
                ));
            }
        }
    }
    let (rewritten, changed) = results.pop().expect("root rewrite result");
    debug_assert!(results.is_empty());
    changed
        .then_some(rewritten)
        .ok_or_else(|| {
            if blocked_by_binder {
                "`rewrite` cannot substitute an equality through a quantifier that binds one of its variables".to_string()
            } else {
                "`rewrite` equality does not occur in the current goal".to_string()
            }
        })
}

/// One byte, one name: an admitted `int8(u) == k`, with `u` a byte load and
/// `k` in `-128..=127`, rewrites as `u == k mod 256`.
///
/// A signed byte read is `Bitvector32Term::signed_byte(u)`, the conversion
/// of the byte's single (unsigned) name `u`, so every occurrence of the
/// signed read contains `u`. Substituting `u` therefore rewrites both the
/// signed reads (`int8(k mod 256)` folds back to `k`) and the unsigned reads
/// the original equality could not reach. Soundness: a `UInt8` load holds one
/// zero-extended byte, `0..=255`, and the conversion maps that range
/// bijectively onto `-128..=127`, so `int8(u) == k` holds exactly when
/// `u == k mod 256`. A constant outside `-128..=127` is the conversion of no
/// byte; that equality is kept as written and never becomes a satisfiable
/// byte equality. The reverse orientation `k == int8(u)`, which replaces a
/// constant, is also kept as written. The check is the equality's own two
/// operands; nothing else is consulted.
fn signed_byte_equality_as_byte_equality(equality: &Proposition) -> Option<Proposition> {
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(from, to), true) = equality else {
        return None;
    };
    let byte = from.signed_byte_operand()?;
    if !matches!(
        crate::kernel::eval::viewed_as_memory_load(byte),
        Some(Bitvector32Term::MemoryLoad(_, _, LoadKind::UInt8))
    ) {
        return None;
    }
    let signed = i8::try_from(to.as_const()? as i32).ok()?;
    Some(Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(byte.clone()),
            Box::new(Bitvector32Term::Constant(u32::from(signed as u8))),
        ),
        true,
    ))
}

/// Whether rewriting by this equality cannot change any goal: it states
/// that a term equals itself, or it has already simplified to `true`.
///
/// Both arise when the prover resolves two forms a proof script still
/// distinguishes. The step is then vacuous rather than wrong, so it must not
/// be reported as a missing occurrence or an unsupported equality shape.
fn equality_is_vacuous(equality: &Proposition) -> bool {
    if matches!(
        equality,
        Proposition::ConditionIs(ConditionTerm::Constant(true), true)
    ) {
        return true;
    }
    match equality {
        Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) => left == right,
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) => {
            left == right
        }
        Proposition::ConditionIs(ConditionTerm::Bitvector64Equal(left, right), true) => {
            left == right
        }
        Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true) => left == right,
        Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(left, right), true) => {
            left == right
        }
        Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true) => left == right,
        _ => false,
    }
}

/// `rewrite` looks through a load variable: the rewritten term may occur
/// inside the address of the load the variable stands for. Rewriting that
/// address and taking the canonical form of the rewritten load gives the
/// load variable (or recorded value) for the rewritten read — equality
/// substitution is congruent through a load whether the load is written as a
/// term or named by its variable. Deterministic: the registry view and the
/// canonical form are the same on check.
fn rewrite_through_load_variable(
    term: &Bitvector32Term,
    rewrite_pointer: &impl Fn(&Pointer) -> Pointer,
) -> Option<Bitvector32Term> {
    let Bitvector32Term::Variable(variable) = term else {
        return None;
    };
    if !crate::kernel::is_load_variable(variable) {
        return None;
    }
    // Rewrite the address at the snapshot where this load was observed.
    // Its canonical snapshot may be a projected placeholder: it preserves
    // the original cell's value, but need not preserve a different address
    // exposed by the equality. The current epoch's origin retains that
    // execution history, just as it does for checked load transport.
    // Without a live origin, keep the variable's defining snapshot.
    let (memory, pointer) = crate::kernel::registered_load_origin_for_variable(variable)
        .or_else(|| crate::kernel::registered_load_for_variable(variable))?;
    let kind = crate::kernel::registered_load_kind_for_variable(variable)?;
    let rewritten = rewrite_pointer(&pointer);
    if rewritten == pointer {
        return None;
    }
    Some(crate::kernel::canonical_term(&Bitvector32Term::MemoryLoad(
        memory,
        Box::new(rewritten),
        kind,
    )))
}

/// A producer-registered pointer read denotes a whole value. Its legacy
/// storage block is not a base to which an alias displacement can be added.
/// Rewrite the read's address instead, then name that read at its original
/// snapshot. A projected snapshot only preserves its original selected cell.
fn rewrite_through_registered_pointer_read(
    pointer: &Pointer,
    rewrite_address: &impl Fn(&Pointer) -> Pointer,
) -> Option<Pointer> {
    // Opaque pointer-load blocks already have their own rewrite below.
    // Only the legacy storage-relative representation needs this distinction.
    pointer.as_loaded()?;
    let Bitvector32Term::MemoryLoad(memory, address, _) =
        crate::kernel::equality_graph::logical_pointer_read_term(pointer)?
    else {
        return None;
    };
    let (source, address) = crate::kernel::eval::typed_pointer_read_variable(pointer)
        .and_then(|variable| crate::kernel::registered_load_origin_for_variable(&variable))
        .unwrap_or((memory, *address));
    let rewritten_address = rewrite_address(&address);
    if rewritten_address == address {
        return Some(pointer.clone());
    }
    // A complete typed pointer stored in this exact cell is already the
    // rewritten read's value. No earlier store or alias spelling is searched.
    if let Some(CValue::Pointer(value)) = source.known_value(&rewritten_address) {
        return Some(value.pointer().clone());
    }
    let read = Bitvector32Term::MemoryLoad(
        source.clone(),
        Box::new(rewritten_address.clone()),
        crate::kernel::LoadKind::Bits32,
    );
    // An already named read can use its canonical identity. A cold rewrite
    // keeps the exact snapshot application instead of searching its history.
    let canonical = crate::kernel::eval::known_pointer_read_variable_for_term(&read)
        .and_then(|variable| crate::kernel::registered_load_term_for_variable(&variable));
    Some(match canonical {
        Some(Bitvector32Term::MemoryLoad(memory, address, _)) => {
            Pointer::loaded_value(&memory, &address)
        }
        _ => Pointer::loaded_value(&source, &rewritten_address),
    })
}

/// `rewrite` looks through a loaded pointer the same way: a pointer whose
/// block is the identity of a load (`Pointer::loaded`) is the value of that
/// load, so a rewrite of the load's address gives the rewritten load, and
/// the pointer becomes that load's identity. Nested loads are rewritten
/// through at most `depth` levels.
fn rewrite_through_loaded_pointer_block(
    pointer: &Pointer,
    rewrite_pointer: &impl Fn(&Pointer) -> Pointer,
    depth: usize,
) -> Option<Pointer> {
    let PointerBlock::Symbolic(variable) = &pointer.block else {
        return None;
    };
    if depth == 0 || !crate::kernel::is_load_variable(variable) {
        return None;
    }
    let (memory, address) = crate::kernel::registered_load_origin_for_variable(variable)
        .or_else(|| crate::kernel::registered_load_for_variable(variable))?;
    let kind = crate::kernel::registered_load_kind_for_variable(variable)?;
    let rewritten_address = {
        let direct = rewrite_pointer(&address);
        if direct != address {
            direct
        } else {
            rewrite_through_loaded_pointer_block(&address, rewrite_pointer, depth - 1)?
        }
    };
    let load = crate::kernel::canonical_term(&Bitvector32Term::MemoryLoad(
        memory,
        Box::new(rewritten_address),
        kind,
    ));
    let named = match load {
        Bitvector32Term::Variable(variable) => variable,
        load @ Bitvector32Term::MemoryLoad(_, _, _) => {
            crate::kernel::load_variable_for_term(&load)?.0
        }
        _ => return None,
    };
    Some(Pointer {
        block: PointerBlock::Symbolic(named),
        offset: pointer.offset.clone(),
    })
}

/// Congruence inside pure-function arguments and other explicit logical
/// terms missed by the structural address rewrite. A whole symbolic pointer
/// uses capture-avoiding variable substitution; other pointer equalities use
/// exact matching and refuse internal binders whose scope is unsupported.
/// Neither path searches an ambient proof state or changes load snapshots.
fn pointer_congruence_rewrite(
    goal: &Proposition,
    left: &Pointer,
    right: &Pointer,
) -> Option<Proposition> {
    let mut rewrite = if let PointerBlock::Symbolic(variable) = left.block
        && left.offset == PointerOffsetTerm::Constant(0)
    {
        crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_address_variable(
            variable, right,
        )
    } else {
        crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_exact(left, right)
    };
    // Integer machine observations retain reads as registered variables.
    // Rewrite their selected addresses, keeping the exact snapshot and kind,
    // just as the native-condition path does for the same pointer equality.
    rewrite.enable_registered_load_resolution();
    let rewritten = rewrite.proposition(goal);
    (rewrite.refusal().is_none() && &rewritten != goal).then_some(rewritten)
}

fn pointer_offset_congruence_rewrite(
    goal: &Proposition,
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
) -> Option<Proposition> {
    let mut rewrite = super::term_rewrite::TermRewrite::for_pointer_offset_exact(left, right);
    rewrite.enable_registered_load_resolution();
    let rewritten = rewrite.proposition(goal);
    (rewrite.refusal().is_none() && &rewritten != goal).then_some(rewritten)
}

/// Why one atomic proposition was not rewritten by an equality.
#[derive(Debug)]
enum AtomicRewriteRefusal {
    /// The equality's side does not occur in the proposition: it is left as
    /// it is, and a compound goal may still rewrite elsewhere.
    Absent(String),
    /// The rewrite is not admitted here.
    Refused(String),
}

impl From<String> for AtomicRewriteRefusal {
    fn from(message: String) -> Self {
        Self::Refused(message)
    }
}

impl From<&str> for AtomicRewriteRefusal {
    fn from(message: &str) -> Self {
        Self::Refused(message.to_string())
    }
}

impl From<AtomicRewriteRefusal> for String {
    fn from(refusal: AtomicRewriteRefusal) -> Self {
        match refusal {
            AtomicRewriteRefusal::Absent(message) | AtomicRewriteRefusal::Refused(message) => {
                message
            }
        }
    }
}

fn rewrite_atomic_proposition_by_exact_equality(
    goal: &Proposition,
    equality: &Proposition,
) -> Result<Proposition, AtomicRewriteRefusal> {
    if let Proposition::ConditionIs(ConditionTerm::PointerValueEqual(left, right), true) = equality
    {
        let mut rewrite = super::term_rewrite::TermRewrite::for_pointer_value_exact(left, right);
        let rewritten = rewrite.proposition(goal);
        if rewrite.refusal().is_some() {
            return Err(AtomicRewriteRefusal::Refused(
                "pointer value rewrite exceeded its supported scope".into(),
            ));
        }
        if rewritten != *goal {
            return Ok(rewritten);
        }
        return rewrite_atomic_proposition_by_exact_equality(
            goal,
            &Proposition::ConditionIs(
                ConditionTerm::pointer_equal(left.pointer().clone(), right.pointer().clone()),
                true,
            ),
        );
    }
    if matches!(
        goal,
        Proposition::ConditionIs(ConditionTerm::PointerValueEqual(..), _)
    ) && let Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(left, right) | ConditionTerm::Bitvector64Equal(left, right),
        true,
    ) = equality
    {
        let mut rewrite = super::term_rewrite::TermRewrite::for_bits(left, right);
        let rewritten = rewrite.proposition(goal);
        if rewrite.refusal().is_none() && rewritten != *goal {
            return Ok(rewritten);
        }
    }
    fn rewrite_c_value(
        value: &CValue,
        rewrite_term: &impl Fn(&Bitvector32Term) -> Bitvector32Term,
        rewrite_pointer: &impl Fn(&Pointer) -> Pointer,
    ) -> CValue {
        match value {
            CValue::PointerInteger(record) => CValue::PointerInteger(PointerIntegerValue {
                kind: record.kind.clone(),
                numeric: Box::new(rewrite_c_value(
                    &record.numeric,
                    rewrite_term,
                    rewrite_pointer,
                )),
                pointer: Box::new(record.pointer.map_addresses(rewrite_pointer)),
            }),
            CValue::Parameter(term) => CValue::Parameter(Box::new(rewrite_algebraic(
                term,
                rewrite_term,
                rewrite_pointer,
            ))),
            CValue::Void => CValue::Void,
            CValue::Bool(term) => CValue::Bool(rewrite_term(term)),
            CValue::Int8(term) => CValue::Int8(rewrite_term(term)),
            CValue::Int16(term) => CValue::Int16(rewrite_term(term)),
            CValue::Int32(term) => CValue::Int32(rewrite_term(term)),
            CValue::UInt8(term) => CValue::UInt8(rewrite_term(term)),
            CValue::UInt16(term) => CValue::UInt16(rewrite_term(term)),
            CValue::UInt32(term) => CValue::UInt32(rewrite_term(term)),
            CValue::Int64(term) => CValue::Int64(rewrite_term(term)),
            CValue::UInt64(term) => CValue::UInt64(rewrite_term(term)),
            CValue::Int128(term) => CValue::Int128(rewrite_term(term)),
            CValue::UInt128(term) => CValue::UInt128(rewrite_term(term)),
            CValue::Float32(term) => CValue::Float32(rewrite_term(term)),
            CValue::Float64(term) => CValue::Float64(rewrite_term(term)),
            CValue::Pointer(pointer) => CValue::Pointer(pointer.map_addresses(rewrite_pointer)),
        }
    }

    fn rewrite_algebraic(
        term: &AlgebraicTerm,
        rewrite_term: &impl Fn(&Bitvector32Term) -> Bitvector32Term,
        rewrite_pointer: &impl Fn(&Pointer) -> Pointer,
    ) -> AlgebraicTerm {
        let node = match &term.node {
            AlgebraicTermNode::Variable(variable) => AlgebraicTermNode::Variable(*variable),
            AlgebraicTermNode::MemoryLoad { memory, pointer } => AlgebraicTermNode::MemoryLoad {
                memory: memory.clone(),
                pointer: Box::new(rewrite_pointer(pointer)),
            },
            AlgebraicTermNode::Constructor { variant, fields } => AlgebraicTermNode::Constructor {
                variant: variant.clone(),
                fields: fields
                    .iter()
                    .map(|field| rewrite_algebraic_value(field, rewrite_term, rewrite_pointer))
                    .collect(),
            },
            AlgebraicTermNode::Match { scrutinee, arms } => AlgebraicTermNode::Match {
                scrutinee: Box::new(rewrite_algebraic(scrutinee, rewrite_term, rewrite_pointer)),
                arms: arms
                    .iter()
                    .map(|arm| AlgebraicResultMatchArm {
                        variant: arm.variant.clone(),
                        bindings: arm
                            .bindings
                            .iter()
                            .map(|binding| {
                                rewrite_algebraic_value(binding, rewrite_term, rewrite_pointer)
                            })
                            .collect(),
                        body: rewrite_algebraic(&arm.body, rewrite_term, rewrite_pointer),
                    })
                    .collect(),
            },
            AlgebraicTermNode::PureFunctionApplication { name, arguments } => {
                AlgebraicTermNode::PureFunctionApplication {
                    name: name.clone(),
                    arguments: arguments
                        .iter()
                        .map(|argument| match argument {
                            PureFunctionArgument::Value(value) => PureFunctionArgument::Value(
                                rewrite_c_value(value, rewrite_term, rewrite_pointer),
                            ),
                            PureFunctionArgument::Algebraic(value) => {
                                PureFunctionArgument::Algebraic(rewrite_algebraic(
                                    value,
                                    rewrite_term,
                                    rewrite_pointer,
                                ))
                            }
                            PureFunctionArgument::Integer(value) => {
                                PureFunctionArgument::Integer(value.clone())
                            }
                            PureFunctionArgument::ArrayRef {
                                memory,
                                pointer,
                                element_type,
                            } => PureFunctionArgument::ArrayRef {
                                memory: memory.clone(),
                                pointer: rewrite_c_value(pointer, rewrite_term, rewrite_pointer),
                                element_type: *element_type,
                            },
                        })
                        .collect(),
                }
            }
            AlgebraicTermNode::If {
                condition,
                then_term,
                else_term,
            } => {
                return AlgebraicTerm::if_then_else(
                    crate::kernel::rewrite_condition_through_bits(condition, rewrite_term),
                    rewrite_algebraic(then_term, rewrite_term, rewrite_pointer),
                    rewrite_algebraic(else_term, rewrite_term, rewrite_pointer),
                );
            }
        };
        AlgebraicTerm {
            algebraic_type: term.algebraic_type.clone(),
            node,
        }
    }

    fn rewrite_algebraic_value(
        value: &AlgebraicValue,
        rewrite_term: &impl Fn(&Bitvector32Term) -> Bitvector32Term,
        rewrite_pointer: &impl Fn(&Pointer) -> Pointer,
    ) -> AlgebraicValue {
        match value {
            AlgebraicValue::C(value) => {
                AlgebraicValue::C(rewrite_c_value(value, rewrite_term, rewrite_pointer))
            }
            AlgebraicValue::Integer(value) => AlgebraicValue::Integer(value.clone()),
            AlgebraicValue::Algebraic(value) => {
                AlgebraicValue::Algebraic(rewrite_algebraic(value, rewrite_term, rewrite_pointer))
            }
        }
    }

    if let Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true) = equality {
        let mut rewrite = super::term_rewrite::TermRewrite::for_integer_exact(left, right);
        let rewritten = rewrite.proposition(goal);
        match rewrite.refusal() {
            Some(super::term_rewrite::RewriteRefusal::WorkExhausted) => {
                return Err(
                    "`rewrite` exhausted its work budget while rewriting Integer terms".into(),
                );
            }
            Some(super::term_rewrite::RewriteRefusal::UnsupportedScope) => {
                return Err("`rewrite` cannot substitute an Integer equality through an internal fold or match binder".into());
            }
            None => {}
        }
        if !rewrite.changed {
            return Err(AtomicRewriteRefusal::Absent(
                "`rewrite` equality does not occur in the current goal".to_string(),
            ));
        }
        return Ok(rewritten);
    }

    if let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) = equality {
        let mut rewrite = super::term_rewrite::TermRewrite::new(left, right);
        let rewritten = match goal {
            Proposition::Equal(a, b) => Proposition::Equal(rewrite.term(a), rewrite.term(b)),
            Proposition::ConditionIs(c, expected) => {
                Proposition::ConditionIs(rewrite.condition(c), *expected)
            }
            _ => {
                return Err(AtomicRewriteRefusal::Absent(
                    "`rewrite` algebraic equality does not occur in this goal".to_string(),
                ));
            }
        };
        if rewrite.refusal().is_some() {
            // A refused scope or exhausted work leaves placeholders in the
            // walker's result; it is not a rewritten goal.
            return Err(
                "`rewrite` cannot substitute this equality through a binder in the current goal"
                    .into(),
            );
        }
        if !rewrite.changed {
            return Err(AtomicRewriteRefusal::Absent(
                "`rewrite` equality does not occur in the current goal".to_string(),
            ));
        }
        return Ok(rewritten);
    }

    if let Proposition::ConditionIs(condition, true) = equality
        && let Some((left, right)) = condition.pointer_offset_sides()
    {
        fn rewrite_offset(
            offset: &PointerOffsetTerm,
            left: &PointerOffsetTerm,
            right: &PointerOffsetTerm,
        ) -> PointerOffsetTerm {
            if offset == left
                // Load variables and load terms of one atom are
                // the same occurrence.
                || crate::kernel::offsets_have_same_canonical_form(offset, left)
            {
                return right.clone();
            }
            match offset {
                PointerOffsetTerm::Add(first, second) => PointerOffsetTerm::add(
                    rewrite_offset(first, left, right),
                    rewrite_offset(second, left, right),
                ),
                // A scaled index may be a load variable whose own address
                // names the rewritten offset (`p->q->cells[i]` under
                // `p->q == r`): rewrite through it, as through the outer
                // load. Each level is the registered address of one load.
                PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                    let rewritten = rewrite_term_offset(value, left, right);
                    if &rewritten == value.as_ref() {
                        offset.clone()
                    } else {
                        PointerOffsetTerm::scale_int32(rewritten, *byte_width)
                    }
                }
                PointerOffsetTerm::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                } => {
                    let rewritten = rewrite_term_offset(value, left, right);
                    if &rewritten == value.as_ref() {
                        offset.clone()
                    } else {
                        PointerOffsetTerm::scale_int64(rewritten, *byte_width, *unsigned)
                    }
                }
                PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => offset.clone(),
            }
        }
        fn rewrite_term_offset(
            term: &Bitvector32Term,
            left: &PointerOffsetTerm,
            right: &PointerOffsetTerm,
        ) -> Bitvector32Term {
            let rewrite_pointer = |pointer: &Pointer| Pointer {
                block: pointer.block.clone(),
                offset: rewrite_offset(&pointer.offset, left, right),
            };
            match term {
                Bitvector32Term::PureFunctionApplication { name, arguments } => {
                    Bitvector32Term::PureFunctionApplication {
                        name: name.clone(),
                        arguments: arguments
                            .iter()
                            .map(|argument| rewrite_term_offset(argument, left, right))
                            .collect(),
                    }
                }
                Bitvector32Term::MemoryLoad(memory, pointer, kind) => Bitvector32Term::MemoryLoad(
                    memory.clone(),
                    Box::new(rewrite_pointer(pointer)),
                    *kind,
                ),
                Bitvector32Term::PointerAddress(pointer, class) => {
                    Bitvector32Term::object_pointer_address(rewrite_pointer(pointer), class.class())
                }
                Bitvector32Term::Variable(_) => {
                    rewrite_through_load_variable(term, &rewrite_pointer)
                        .unwrap_or_else(|| term.clone())
                }
                Bitvector32Term::If { .. }
                | Bitvector32Term::RangeFold { .. }
                | Bitvector32Term::ClickFunctionApplication { .. }
                | Bitvector32Term::AlgebraicMatch { .. }
                | Bitvector32Term::IntegerToMachine { .. }
                | Bitvector32Term::Constant(_)
                | Bitvector32Term::Int64Constant(_)
                | Bitvector32Term::UInt64Constant(_)
                | Bitvector32Term::MachineIntegerConstant(_) => term.clone(),
                term => match (term.as_binary(), term.as_unary()) {
                    // The 32-bit word operators are rebuilt as bare nodes, the rest
                    // through their smart constructors.
                    (Some((op, lhs, rhs)), _) if op.is_bitvector32() => op.build_raw(
                        rewrite_term_offset(lhs, left, right),
                        rewrite_term_offset(rhs, left, right),
                    ),
                    (Some((op, lhs, rhs)), _) => op.build(
                        rewrite_term_offset(lhs, left, right),
                        rewrite_term_offset(rhs, left, right),
                    ),
                    (_, Some((op, operand))) if op.is_bitvector32() => {
                        op.build_raw(rewrite_term_offset(operand, left, right))
                    }
                    (_, Some((op, operand))) => op.build(rewrite_term_offset(operand, left, right)),
                    _ => unreachable!("every other variant has its own arm"),
                },
            }
        }
        fn rewrite_resource_offset(
            resource: &CResource,
            left: &PointerOffsetTerm,
            right: &PointerOffsetTerm,
        ) -> CResource {
            match resource {
                CResource::Memory(range) => CResource::Memory(range.with_bounds(
                    Pointer {
                        block: range.base().block.clone(),
                        offset: rewrite_offset(&range.base().offset, left, right),
                    },
                    rewrite_term_offset(range.bound_terms().0, left, right),
                    rewrite_term_offset(range.bound_terms().1, left, right),
                )),
                CResource::Composite { .. }
                | CResource::Token { .. }
                | CResource::PopulationAuthority(_)
                | CResource::Instance(_)
                | CResource::MutexGuard(_)
                | CResource::MutexLive(_)
                | CResource::MutexUse(_)
                | CResource::Publication(_)
                | CResource::Iterated(_) => resource.clone(),
            }
        }
        let rewritten = match goal {
            Proposition::CMemoryLoadable {
                memory,
                base,
                bytes,
                wide,
            } => Proposition::CMemoryLoadable {
                // Same-block pointer equalities use offsets rather than the
                // PointerEqual carrier. Substitute the selected address while
                // retaining the exact snapshot and readable byte extent.
                memory: memory.clone(),
                base: Pointer {
                    block: base.block.clone(),
                    offset: rewrite_offset(&base.offset, left, right),
                },
                bytes: bytes.clone(),
                wide: *wide,
            },
            Proposition::ConditionIs(
                ConditionTerm::PointerOffsetEqual(goal_left, goal_right),
                expected,
            ) => Proposition::ConditionIs(
                ConditionTerm::PointerOffsetEqual(
                    Box::new(rewrite_offset(goal_left, left, right)),
                    Box::new(rewrite_offset(goal_right, left, right)),
                ),
                *expected,
            ),
            Proposition::ConditionIs(
                ConditionTerm::PointerEqual(goal_left, goal_right),
                expected,
            ) => {
                let rewrite_pointer = |pointer: &Pointer| Pointer {
                    block: pointer.block.clone(),
                    offset: rewrite_offset(&pointer.offset, left, right),
                };
                Proposition::ConditionIs(
                    ConditionTerm::pointer_equal(
                        rewrite_pointer(goal_left),
                        rewrite_pointer(goal_right),
                    ),
                    *expected,
                )
            }
            Proposition::ConditionIs(condition, expected) => {
                let rewrite_term = |term: &Bitvector32Term| rewrite_term_offset(term, left, right);
                let rewritten = match condition {
                    ConditionTerm::Bitvector32SignedLessThan(left, right) => {
                        ConditionTerm::Bitvector32SignedLessThan(
                            Box::new(rewrite_term(left)),
                            Box::new(rewrite_term(right)),
                        )
                    }
                    ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
                        ConditionTerm::Bitvector32SignedLessEqual(
                            Box::new(rewrite_term(left)),
                            Box::new(rewrite_term(right)),
                        )
                    }
                    ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
                        ConditionTerm::Bitvector32SignedGreaterThan(
                            Box::new(rewrite_term(left)),
                            Box::new(rewrite_term(right)),
                        )
                    }
                    ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
                        ConditionTerm::Bitvector32SignedGreaterEqual(
                            Box::new(rewrite_term(left)),
                            Box::new(rewrite_term(right)),
                        )
                    }
                    ConditionTerm::Bitvector32Equal(left, right) => {
                        ConditionTerm::Bitvector32Equal(
                            Box::new(rewrite_term(left)),
                            Box::new(rewrite_term(right)),
                        )
                    }
                    ConditionTerm::Bitvector64Equal(left, right) => {
                        ConditionTerm::Bitvector64Equal(
                            Box::new(rewrite_term(left)),
                            Box::new(rewrite_term(right)),
                        )
                    }
                    _ => {
                        return pointer_offset_congruence_rewrite(goal, left, right).ok_or_else(
                            || {
                                AtomicRewriteRefusal::Absent(
                                    "`rewrite` pointer-offset equality does not occur in this goal"
                                        .to_string(),
                                )
                            },
                        );
                    }
                };
                Proposition::ConditionIs(rewritten, *expected)
            }
            Proposition::CResourceSeparate {
                left: goal_left,
                right: goal_right,
            } => Proposition::CResourceSeparate {
                left: Box::new(rewrite_resource_offset(goal_left, left, right)),
                right: Box::new(rewrite_resource_offset(goal_right, left, right)),
            },
            Proposition::CResourceContains { parent, child } => Proposition::CResourceContains {
                parent: Box::new(rewrite_resource_offset(parent, left, right)),
                child: Box::new(rewrite_resource_offset(child, left, right)),
            },
            Proposition::Equal(Term::Algebraic(goal_left), Term::Algebraic(goal_right)) => {
                let rewrite_term = |term: &Bitvector32Term| rewrite_term_offset(term, left, right);
                let rewrite_pointer = |pointer: &Pointer| Pointer {
                    block: pointer.block.clone(),
                    offset: rewrite_offset(&pointer.offset, left, right),
                };
                Proposition::Equal(
                    Term::Algebraic(rewrite_algebraic(
                        goal_left,
                        &rewrite_term,
                        &rewrite_pointer,
                    )),
                    Term::Algebraic(rewrite_algebraic(
                        goal_right,
                        &rewrite_term,
                        &rewrite_pointer,
                    )),
                )
            }
            _ => {
                return pointer_offset_congruence_rewrite(goal, left, right).ok_or_else(|| {
                    AtomicRewriteRefusal::Absent(
                        "`rewrite` pointer-offset equality does not occur in this goal".to_string(),
                    )
                });
            }
        };
        if &rewritten == goal {
            return pointer_offset_congruence_rewrite(goal, left, right).ok_or_else(|| {
                AtomicRewriteRefusal::Absent(
                    "`rewrite` equality does not occur in the current goal".to_string(),
                )
            });
        }
        return Ok(rewritten);
    }
    if let Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true) = equality {
        // A field or array access keeps its base pointer's block and adds a
        // displacement. An equality of the bases therefore also rewrites the
        // address of that access, with the same displacement on the right.
        // Match one structural suffix; do not search the ambient pointer
        // equalities or change the memory snapshot of a load.
        fn offset_after_base(
            address: &PointerOffsetTerm,
            base: &PointerOffsetTerm,
        ) -> Option<PointerOffsetTerm> {
            if base == &PointerOffsetTerm::Constant(0) {
                return Some(address.clone());
            }
            // Keep parent links rather than cloning a growing suffix at each
            // Add node. A deeply nested address costs one walk plus one
            // construction of the matched displacement.
            struct OffsetNode<'a> {
                offset: &'a PointerOffsetTerm,
                parent: Option<usize>,
                sibling: Option<&'a PointerOffsetTerm>,
            }
            let mut nodes = vec![OffsetNode {
                offset: address,
                parent: None,
                sibling: None,
            }];
            let mut pending = vec![0];
            while let Some(index) = pending.pop() {
                let offset = nodes[index].offset;
                let difference = if offset == base {
                    Some(PointerOffsetTerm::Constant(0))
                } else if let (
                    PointerOffsetTerm::Constant(address),
                    PointerOffsetTerm::Constant(base),
                ) = (offset, base)
                {
                    address.checked_sub(*base).map(PointerOffsetTerm::Constant)
                } else {
                    None
                };
                if let Some(mut difference) = difference {
                    let mut cursor = index;
                    while let Some(parent) = nodes[cursor].parent {
                        difference =
                            add_pointer_offsets(difference, nodes[cursor].sibling?.clone())?;
                        cursor = parent;
                    }
                    return Some(difference);
                }
                if let PointerOffsetTerm::Add(left, right) = offset {
                    let left_index = nodes.len();
                    nodes.push(OffsetNode {
                        offset: left,
                        parent: Some(index),
                        sibling: Some(right),
                    });
                    let right_index = nodes.len();
                    nodes.push(OffsetNode {
                        offset: right,
                        parent: Some(index),
                        sibling: Some(left),
                    });
                    pending.push(right_index);
                    pending.push(left_index);
                }
            }
            None
        }
        fn add_pointer_offsets(
            left: PointerOffsetTerm,
            right: PointerOffsetTerm,
        ) -> Option<PointerOffsetTerm> {
            use PointerOffsetTerm::{Add, Constant};
            match (left, right) {
                (Constant(0), other) | (other, Constant(0)) => Some(other),
                (Constant(left), Constant(right)) => left.checked_add(right).map(Constant),
                (Add(base, trailing), Constant(right))
                    if matches!(trailing.as_ref(), Constant(_)) =>
                {
                    let Constant(trailing) = *trailing else {
                        unreachable!()
                    };
                    let combined = trailing.checked_add(right)?;
                    if combined == 0 {
                        Some(*base)
                    } else {
                        Some(Add(base, Box::new(Constant(combined))))
                    }
                }
                (left, right) => Some(Add(Box::new(left), Box::new(right))),
            }
        }
        let rewrite_pointer_directly = |pointer: &Pointer| {
            if pointer == left.as_ref() {
                return right.as_ref().clone();
            }
            if pointer.block != left.block {
                return pointer.clone();
            }
            let Some(displacement) = offset_after_base(&pointer.offset, &left.offset) else {
                return pointer.clone();
            };
            let Some(offset) = add_pointer_offsets(right.offset.clone(), displacement) else {
                return pointer.clone();
            };
            Pointer {
                block: right.block.clone(),
                offset,
            }
        };
        let rewrite_pointer = |pointer: &Pointer| {
            if pointer == left.as_ref() {
                return right.as_ref().clone();
            }
            if let Some(rewritten) =
                rewrite_through_registered_pointer_read(pointer, &rewrite_pointer_directly)
            {
                return rewritten;
            }
            let rewritten = rewrite_pointer_directly(pointer);
            if &rewritten != pointer {
                return rewritten;
            }
            rewrite_through_loaded_pointer_block(pointer, &rewrite_pointer_directly, 8)
                .unwrap_or(rewritten)
        };
        // A pointer equality also rewrites the subject of a load: replacing
        // the loaded pointer with its proven-equal form is exact term
        // congruence, with work bounded by the goal's size.
        fn rewrite_load_pointers(
            term: &Bitvector32Term,
            rewrite_pointer: &impl Fn(&Pointer) -> Pointer,
        ) -> Bitvector32Term {
            let binary = |left_term: &Bitvector32Term, right_term: &Bitvector32Term| {
                (
                    Box::new(rewrite_load_pointers(left_term, rewrite_pointer)),
                    Box::new(rewrite_load_pointers(right_term, rewrite_pointer)),
                )
            };
            match term {
                Bitvector32Term::MemoryLoad(memory, pointer, kind) => Bitvector32Term::MemoryLoad(
                    memory.clone(),
                    Box::new(rewrite_pointer(pointer)),
                    *kind,
                ),
                Bitvector32Term::Variable(_) => {
                    rewrite_through_load_variable(term, rewrite_pointer)
                        .unwrap_or_else(|| term.clone())
                }
                Bitvector32Term::Add(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::Add(left, right)
                }
                Bitvector32Term::Subtract(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::Subtract(left, right)
                }
                Bitvector32Term::Multiply(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::Multiply(left, right)
                }
                Bitvector32Term::Divide(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::Divide(left, right)
                }
                Bitvector32Term::Remainder(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::Remainder(left, right)
                }
                _ => term.clone(),
            }
        }
        let rewritten = match goal {
            Proposition::CMemoryLoadable {
                memory,
                base,
                bytes,
                wide,
            } => {
                Proposition::CMemoryLoadable {
                    // Clone only shared snapshot roots. Equality changes the
                    // selected address, never the memory or view extent.
                    memory: memory.clone(),
                    base: rewrite_pointer(base),
                    bytes: bytes.clone(),
                    wide: *wide,
                }
            }
            Proposition::ConditionIs(
                ConditionTerm::PointerEqual(goal_left, goal_right),
                expected,
            ) => Proposition::ConditionIs(
                // Replacing one side can land both pointers in the same
                // block, and a same-block pointer equality is carried
                // everywhere else as the equality of its offsets. Rebuild
                // through the canonicalizing constructor so the rewritten
                // goal is the term an ordinary lowering would produce and a
                // later `assumption` or `normalize() using` can see it.
                ConditionTerm::pointer_equal(
                    rewrite_pointer(goal_left),
                    rewrite_pointer(goal_right),
                ),
                *expected,
            ),
            Proposition::ConditionIs(
                ConditionTerm::PointerValueEqual(goal_left, goal_right),
                expected,
            ) => Proposition::ConditionIs(
                ConditionTerm::PointerValueEqual(
                    Box::new(goal_left.map_addresses(&rewrite_pointer)),
                    Box::new(goal_right.map_addresses(&rewrite_pointer)),
                ),
                *expected,
            ),
            Proposition::ConditionIs(condition, expected) => {
                let rewrite_term =
                    |term: &Bitvector32Term| rewrite_load_pointers(term, &rewrite_pointer);
                let rewritten = match condition {
                    ConditionTerm::Bitvector32SignedLessThan(goal_left, goal_right) => {
                        ConditionTerm::Bitvector32SignedLessThan(
                            Box::new(rewrite_term(goal_left)),
                            Box::new(rewrite_term(goal_right)),
                        )
                    }
                    ConditionTerm::Bitvector32SignedLessEqual(goal_left, goal_right) => {
                        ConditionTerm::Bitvector32SignedLessEqual(
                            Box::new(rewrite_term(goal_left)),
                            Box::new(rewrite_term(goal_right)),
                        )
                    }
                    ConditionTerm::Bitvector32SignedGreaterThan(goal_left, goal_right) => {
                        ConditionTerm::Bitvector32SignedGreaterThan(
                            Box::new(rewrite_term(goal_left)),
                            Box::new(rewrite_term(goal_right)),
                        )
                    }
                    ConditionTerm::Bitvector32SignedGreaterEqual(goal_left, goal_right) => {
                        ConditionTerm::Bitvector32SignedGreaterEqual(
                            Box::new(rewrite_term(goal_left)),
                            Box::new(rewrite_term(goal_right)),
                        )
                    }
                    ConditionTerm::Bitvector32Equal(goal_left, goal_right) => {
                        ConditionTerm::Bitvector32Equal(
                            Box::new(rewrite_term(goal_left)),
                            Box::new(rewrite_term(goal_right)),
                        )
                    }
                    _ => {
                        return pointer_congruence_rewrite(goal, left, right).ok_or_else(|| {
                            AtomicRewriteRefusal::Absent(
                                "`rewrite` pointer equality does not occur in this goal"
                                    .to_string(),
                            )
                        });
                    }
                };
                Proposition::ConditionIs(rewritten, *expected)
            }
            Proposition::Equal(Term::Algebraic(goal_left), Term::Algebraic(goal_right)) => {
                let rewrite_term =
                    |term: &Bitvector32Term| rewrite_load_pointers(term, &rewrite_pointer);
                Proposition::Equal(
                    Term::Algebraic(rewrite_algebraic(
                        goal_left,
                        &rewrite_term,
                        &rewrite_pointer,
                    )),
                    Term::Algebraic(rewrite_algebraic(
                        goal_right,
                        &rewrite_term,
                        &rewrite_pointer,
                    )),
                )
            }
            _ => {
                return pointer_congruence_rewrite(goal, left, right)
                    .ok_or_else(|| "`rewrite` pointer equality expects a condition goal".into());
            }
        };
        if &rewritten == goal {
            return pointer_congruence_rewrite(goal, left, right).ok_or_else(|| {
                AtomicRewriteRefusal::Absent(
                    "`rewrite` equality does not occur in the current goal".to_string(),
                )
            });
        }
        return Ok(rewritten);
    }
    let (left, right) = match equality {
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) => {
            (left, right)
        }
        Proposition::ConditionIs(ConditionTerm::Bitvector64Equal(left, right), true) => {
            (left, right)
        }
        _ => return Err("`rewrite` expects a mathematical Integer, native 32-bit/64-bit, pointer, or algebraic equality".into()),

    };
    // Address annotations describe a producer's object class, not the bits
    // observed by a numeric equality. Keep the pointer and mask themselves
    // exact; no pointer-value or memory-snapshot identity is substituted.
    fn same_address_observation(left: &Bitvector32Term, right: &Bitvector32Term) -> bool {
        fn key(term: &Bitvector32Term) -> Option<(&Pointer, Option<u64>)> {
            if let Some(pointer) = term.address_pointer() {
                return Some((pointer, None));
            }
            let Bitvector32Term::UInt64BitwiseAnd(left, right) = term else {
                return None;
            };
            let (pointer, mask) = if let Some(pointer) = left.address_pointer() {
                (pointer, right.as_ref())
            } else {
                (right.address_pointer()?, left.as_ref())
            };
            Some((pointer, Some(mask.uint64_as_const()?)))
        }
        matches!((key(left), key(right)), (Some(a), Some(b)) if a == b)
    }
    fn rewrite_term(
        term: &Bitvector32Term,
        from: &Bitvector32Term,
        to: &Bitvector32Term,
    ) -> Bitvector32Term {
        fn rewrite_offset(
            offset: &PointerOffsetTerm,
            from: &Bitvector32Term,
            to: &Bitvector32Term,
        ) -> PointerOffsetTerm {
            match offset {
                PointerOffsetTerm::Add(left, right) => PointerOffsetTerm::add(
                    rewrite_offset(left, from, to),
                    rewrite_offset(right, from, to),
                ),
                PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                    PointerOffsetTerm::scale_int32(rewrite_term(value, from, to), *byte_width)
                }
                PointerOffsetTerm::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                } => PointerOffsetTerm::scale_int64(
                    rewrite_term(value, from, to),
                    *byte_width,
                    *unsigned,
                ),
                PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => offset.clone(),
            }
        }
        if term == from
            || same_address_observation(term, from)
            // Load variables and load terms of one atom are the
            // same occurrence.
            || crate::kernel::terms_have_same_canonical_form(term, from)
        {
            return to.clone();
        }
        // Widening a literal folds away the cast node. Recover only a
        // matching, checked 32-to-64-bit cast of the cited constant; the
        // replacement keeps that cast, including its signedness. Never
        // identify a full-width literal by truncating it to 32 bits.
        if let Bitvector32Term::Constant(source) = from {
            // Unsigned 32-bit order is encoded by signed order after XOR
            // with the sign bit. The constant side of that bias is folded.
            if matches!(term, Bitvector32Term::Constant(value) if *value == source ^ 0x8000_0000) {
                return Bitvector32Term::bitwise_xor(
                    to.clone(),
                    Bitvector32Term::Constant(0x8000_0000),
                );
            }
            let casts: &[fn(Bitvector32Term) -> Bitvector32Term] = match term {
                Bitvector32Term::Int64Constant(_) => &[
                    Bitvector32Term::int64_from_32,
                    Bitvector32Term::int64_from_uint32,
                ],
                Bitvector32Term::UInt64Constant(_) => &[
                    Bitvector32Term::uint64_from_32,
                    Bitvector32Term::uint64_from_int32,
                ],
                _ => &[],
            };
            for cast in casts {
                if cast(from.clone()) == *term {
                    return cast(to.clone());
                }
            }
        }
        let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
            (
                Box::new(rewrite_term(left, from, to)),
                Box::new(rewrite_term(right, from, to)),
            )
        };
        // Substituting a constant can leave a two-constant operation
        // (`0 + 1` after `rewrite(len == 0)` in a `len + 1` goal); folding
        // it is deterministic arithmetic on the rewritten node only, so the
        // rewritten goal states the value the substitution denotes.
        match term {
            Bitvector32Term::Add(left, right) => {
                let (left, right) = binary(left, right);
                match (left.as_ref(), right.as_ref()) {
                    (Bitvector32Term::Constant(first), Bitvector32Term::Constant(second)) => {
                        Bitvector32Term::Constant(first.wrapping_add(*second))
                    }
                    _ => Bitvector32Term::Add(left, right),
                }
            }
            Bitvector32Term::Subtract(left, right) => {
                let (left, right) = binary(left, right);
                match (left.as_ref(), right.as_ref()) {
                    (Bitvector32Term::Constant(first), Bitvector32Term::Constant(second)) => {
                        Bitvector32Term::Constant(first.wrapping_sub(*second))
                    }
                    _ => Bitvector32Term::Subtract(left, right),
                }
            }
            Bitvector32Term::Multiply(left, right) => Bitvector32Term::multiply(
                rewrite_term(left, from, to),
                rewrite_term(right, from, to),
            ),
            Bitvector32Term::BitwiseAnd(left, right) => Bitvector32Term::bitwise_and(
                rewrite_term(left, from, to),
                rewrite_term(right, from, to),
            ),
            Bitvector32Term::ShiftLeft(left, right) => {
                // The term denotes the shifted bits; signed C overflow is
                // checked separately during expression evaluation. Preserve
                // unsigned high-bit results when substitution makes both
                // operands constant.
                Bitvector32Term::unsigned_shift_left(
                    rewrite_term(left, from, to),
                    rewrite_term(right, from, to),
                )
            }
            Bitvector32Term::PureFunctionApplication { name, arguments } => {
                Bitvector32Term::PureFunctionApplication {
                    name: name.clone(),
                    arguments: arguments
                        .iter()
                        .map(|argument| rewrite_term(argument, from, to))
                        .collect(),
                }
            }
            // The memory snapshot is fixed, but its address is an ordinary
            // expression: exact equality substitution is congruent there too.
            Bitvector32Term::MemoryLoad(memory, pointer, kind) => Bitvector32Term::MemoryLoad(
                memory.clone(),
                Box::new(Pointer {
                    block: pointer.block.clone(),
                    offset: rewrite_offset(&pointer.offset, from, to),
                }),
                *kind,
            ),
            Bitvector32Term::PointerAddress(pointer, class) => {
                Bitvector32Term::object_pointer_address(
                    Pointer {
                        block: pointer.block.clone(),
                        offset: rewrite_offset(&pointer.offset, from, to),
                    },
                    class.class(),
                )
            }
            Bitvector32Term::Variable(_) => {
                rewrite_through_load_variable(term, &|pointer| Pointer {
                    block: pointer.block.clone(),
                    offset: rewrite_offset(&pointer.offset, from, to),
                })
                .unwrap_or_else(|| term.clone())
            }
            Bitvector32Term::If { .. }
            | Bitvector32Term::RangeFold { .. }
            | Bitvector32Term::ClickFunctionApplication { .. }
            | Bitvector32Term::AlgebraicMatch { .. }
            | Bitvector32Term::IntegerToMachine { .. } => {
                let mut rewrite = super::term_rewrite::TermRewrite::for_bits(from, to);
                let rewritten = rewrite.bits(term);
                // The walker reports a scope it will not substitute through,
                // or exhausted work, by setting a flag and handing back a
                // placeholder constant. That placeholder is not a rewritten
                // term: keeping it replaced an unfolded `match` by `0` and
                // let `rewrite` close false goals. Declining an occurrence is
                // always a sound substitution, so the term stays as it was.
                if rewrite.refusal().is_some() {
                    term.clone()
                } else {
                    rewritten
                }
            }
            Bitvector32Term::Constant(_)
            | Bitvector32Term::Int64Constant(_)
            | Bitvector32Term::UInt64Constant(_)
            | Bitvector32Term::MachineIntegerConstant(_) => term.clone(),
            term => match (term.as_binary(), term.as_unary()) {
                // The 32-bit word operators are rebuilt as bare nodes, the rest
                // through their smart constructors.
                (Some((op, left, right)), _) if op.is_bitvector32() => {
                    op.build_raw(rewrite_term(left, from, to), rewrite_term(right, from, to))
                }
                (Some((op, left, right)), _) => {
                    op.build(rewrite_term(left, from, to), rewrite_term(right, from, to))
                }
                (_, Some((op, value))) if op.is_bitvector32() => {
                    op.build_raw(rewrite_term(value, from, to))
                }
                (_, Some((op, value))) => op.build(rewrite_term(value, from, to)),
                _ => unreachable!("every other variant has its own arm"),
            },
        }
    }

    fn rewrite_offset_term(
        offset: &PointerOffsetTerm,
        from: &Bitvector32Term,
        to: &Bitvector32Term,
    ) -> PointerOffsetTerm {
        match offset {
            PointerOffsetTerm::Add(left, right) => PointerOffsetTerm::add(
                rewrite_offset_term(left, from, to),
                rewrite_offset_term(right, from, to),
            ),
            PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                PointerOffsetTerm::scale_int32(rewrite_term(value, from, to), *byte_width)
            }
            PointerOffsetTerm::Int64Scaled {
                value,
                byte_width,
                unsigned,
            } => PointerOffsetTerm::scale_int64(
                rewrite_term(value, from, to),
                *byte_width,
                *unsigned,
            ),
            PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => offset.clone(),
        }
    }

    // A mathematical observation of a machine value is still congruent under
    // a checked equality for that machine value.  Keep this bridge narrow:
    // root machine observations, scalar application arguments, and
    // Int32 range-fold endpoints retain their direct substitutions. Arithmetic
    // uses the shared checked, scope-aware walker; a refusal keeps the original
    // term, never a partial result. Re-interning through `from_machine` folds a
    // rewritten constant to the ordinary mathematical constant while
    // retaining the carrier when it remains symbolic.
    fn rewrite_integer_observation(
        term: &SharedIntegerTerm,
        from: &Bitvector32Term,
        to: &Bitvector32Term,
    ) -> SharedIntegerTerm {
        match term.as_ref() {
            IntegerTerm::Machine(machine) => {
                let value = rewrite_term(machine.value(), from, to);
                if value == *machine.value() {
                    return term.clone();
                }
                IntegerTerm::from_machine(machine.ty(), value.clone())
                    .unwrap_or_else(|| {
                        IntegerTerm::Machine(SharedMachineIntegerTerm::intern(machine.ty(), value))
                    })
                    .into()
            }
            IntegerTerm::PureFunctionApplication(application) => {
                // Rewrite scalar arguments, preserving captured array memory
                // and its element type. No snapshot contents are traversed.
                let arguments = application
                    .arguments()
                    .iter()
                    .map(|argument| {
                        let value = match argument {
                            PureFunctionArgument::Value(CValue::Int32(value)) => {
                                CValue::Int32(rewrite_term(value, from, to))
                            }
                            PureFunctionArgument::Value(CValue::UInt32(value)) => {
                                CValue::UInt32(rewrite_term(value, from, to))
                            }
                            PureFunctionArgument::Value(CValue::Int64(value)) => {
                                CValue::Int64(rewrite_term(value, from, to))
                            }
                            PureFunctionArgument::Value(CValue::UInt64(value)) => {
                                CValue::UInt64(rewrite_term(value, from, to))
                            }
                            _ => return argument.clone(),
                        };
                        PureFunctionArgument::Value(value)
                    })
                    .collect();
                IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                    application.name().to_string(),
                    arguments,
                ))
                .into()
            }
            IntegerTerm::RangeFold {
                index:
                    index @ (IntegerRangeFoldIndex::Int32 { start, end }
                    | IntegerRangeFoldIndex::UInt64 { start, end }),
                initial,
                accumulator,
                item,
                body,
            } => {
                let rewritten_start = rewrite_term(start.value(), from, to);
                let rewritten_end = rewrite_term(end.value(), from, to);
                if rewritten_start == *start.value() && rewritten_end == *end.value() {
                    return term.clone();
                }
                IntegerTerm::RangeFold {
                    index: index.with_machine_endpoints(rewritten_start, rewritten_end),
                    initial: initial.clone(),
                    accumulator: *accumulator,
                    item: *item,
                    body: body.clone(),
                }
                .into()
            }
            _ => {
                let mut rewrite = super::term_rewrite::TermRewrite::for_bits_checked(from, to);
                let rewritten = rewrite.integer(term.as_ref());
                if rewrite.refusal().is_some() {
                    term.clone()
                } else {
                    rewritten.into()
                }
            }
        }
    }

    let full_width_equality = matches!(
        equality,
        Proposition::ConditionIs(ConditionTerm::Bitvector64Equal(_, _), true)
    );
    let rewrite_range_bound = |range: &CMemoryRange, bound: &Bitvector32Term| {
        // A narrow equality cannot replace the complete value of a native
        // bound, even when both are represented by the same term variant.
        if range.wide_bounds().is_some() && !full_width_equality {
            bound.clone()
        } else {
            rewrite_term(bound, left, right)
        }
    };
    let rewrite_resource_term = |resource: &CResource| match resource {
        CResource::Memory(range) => CResource::Memory(range.with_bounds(
            Pointer {
                block: range.base().block.clone(),
                offset: rewrite_offset_term(&range.base().offset, left, right),
            },
            rewrite_range_bound(range, range.bound_terms().0),
            rewrite_range_bound(range, range.bound_terms().1),
        )),
        CResource::Composite { .. }
        | CResource::Token { .. }
        | CResource::PopulationAuthority(_)
        | CResource::Instance(_)
        | CResource::MutexGuard(_)
        | CResource::MutexLive(_)
        | CResource::MutexUse(_)
        | CResource::Publication(_)
        | CResource::Iterated(_) => resource.clone(),
    };
    let rewritten = match goal {
        Proposition::ConditionIs(condition, expected) => {
            let rewritten_condition = if let Some((operator, goal_left, goal_right)) =
                condition.as_bitvector_comparison()
            {
                operator.build_raw(
                    rewrite_term(goal_left, left, right),
                    rewrite_term(goal_right, left, right),
                )
            } else {
                match condition {
                    // `to_integer(machine)` is represented as an Integer machine
                    // observation.  Rewrite its selected machine payload through
                    // the already checked C equality, then let the normal
                    // Integer constructor fold a constant observation.
                    ConditionTerm::IntegerEqual(goal_left, goal_right) => {
                        ConditionTerm::IntegerEqual(
                            rewrite_integer_observation(goal_left, left, right),
                            rewrite_integer_observation(goal_right, left, right),
                        )
                    }
                    ConditionTerm::IntegerLessThan(goal_left, goal_right) => {
                        ConditionTerm::IntegerLessThan(
                            rewrite_integer_observation(goal_left, left, right),
                            rewrite_integer_observation(goal_right, left, right),
                        )
                    }
                    ConditionTerm::IntegerLessEqual(goal_left, goal_right) => {
                        ConditionTerm::IntegerLessEqual(
                            rewrite_integer_observation(goal_left, left, right),
                            rewrite_integer_observation(goal_right, left, right),
                        )
                    }
                    ConditionTerm::IntegerGreaterThan(goal_left, goal_right) => {
                        ConditionTerm::IntegerGreaterThan(
                            rewrite_integer_observation(goal_left, left, right),
                            rewrite_integer_observation(goal_right, left, right),
                        )
                    }
                    ConditionTerm::IntegerGreaterEqual(goal_left, goal_right) => {
                        ConditionTerm::IntegerGreaterEqual(
                            rewrite_integer_observation(goal_left, left, right),
                            rewrite_integer_observation(goal_right, left, right),
                        )
                    }
                    ConditionTerm::IntegerNotEqual(goal_left, goal_right) => {
                        ConditionTerm::IntegerNotEqual(
                            rewrite_integer_observation(goal_left, left, right),
                            rewrite_integer_observation(goal_right, left, right),
                        )
                    }
                    // Pointer goals contain the same int32 terms inside their
                    // offsets; substituting the proven equality there is the same
                    // exact term congruence, with work bounded by the goal.
                    ConditionTerm::PointerOffsetEqual(goal_left, goal_right) => {
                        ConditionTerm::PointerOffsetEqual(
                            Box::new(rewrite_offset_term(goal_left, left, right)),
                            Box::new(rewrite_offset_term(goal_right, left, right)),
                        )
                    }
                    ConditionTerm::PointerEqual(goal_left, goal_right) => {
                        let rewrite_pointer = |pointer: &Pointer| Pointer {
                            block: pointer.block.clone(),
                            offset: rewrite_offset_term(&pointer.offset, left, right),
                        };
                        ConditionTerm::pointer_equal(
                            rewrite_pointer(goal_left),
                            rewrite_pointer(goal_right),
                        )
                    }
                    _ => {
                        return Err("`rewrite` cannot substitute this native equality in the selected condition".into());
                    }
                }
            };
            // Rewriting can expose an address mask that the normal
            // comparison constructor canonicalizes. Present that same form.
            let rewritten_condition = if rewritten_condition.as_pointer_alignment().is_some() {
                match rewritten_condition {
                    ConditionTerm::Bitvector64Equal(left, right) => {
                        ConditionTerm::int64_equal(*left, *right)
                    }
                    other => other,
                }
            } else {
                rewritten_condition
            };
            Proposition::ConditionIs(rewritten_condition, *expected)
        }
        Proposition::CResourceSeparate {
            left: goal_left,
            right: goal_right,
        } => Proposition::CResourceSeparate {
            left: Box::new(rewrite_resource_term(goal_left)),
            right: Box::new(rewrite_resource_term(goal_right)),
        },
        Proposition::CResourceContains { parent, child } => Proposition::CResourceContains {
            parent: Box::new(rewrite_resource_term(parent)),
            child: Box::new(rewrite_resource_term(child)),
        },
        Proposition::CMemoryReadDefined {
            memory,
            pointer,
            value_type,
        } => Proposition::CMemoryReadDefined {
            memory: memory.clone(),
            pointer: Pointer {
                block: pointer.block.clone(),
                offset: rewrite_offset_term(&pointer.offset, left, right),
            },
            value_type: *value_type,
        },
        Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
            wide,
        } => Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: Pointer {
                block: base.block.clone(),
                offset: rewrite_offset_term(&base.offset, left, right),
            },
            bytes: rewrite_term(bytes, left, right),
            wide: *wide,
        },
        Proposition::Equal(Term::Algebraic(goal_left), Term::Algebraic(goal_right)) => {
            let rewrite_term = |term: &Bitvector32Term| rewrite_term(term, left, right);
            let rewrite_pointer = |pointer: &Pointer| Pointer {
                block: pointer.block.clone(),
                offset: rewrite_offset_term(&pointer.offset, left, right),
            };
            Proposition::Equal(
                Term::Algebraic(rewrite_algebraic(
                    goal_left,
                    &rewrite_term,
                    &rewrite_pointer,
                )),
                Term::Algebraic(rewrite_algebraic(
                    goal_right,
                    &rewrite_term,
                    &rewrite_pointer,
                )),
            )
        }
        _ => {
            return Err(AtomicRewriteRefusal::Absent(
                "`rewrite` int32 equality does not occur in this goal".to_string(),
            ));
        }
    };
    if &rewritten == goal {
        return Err(AtomicRewriteRefusal::Absent(
            "`rewrite` equality does not occur in the current goal".to_string(),
        ));
    }
    Ok(rewritten)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn equality(left: Bitvector32Term, right: Bitvector32Term) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
            true,
        )
    }

    fn integer_equality(a: IntegerTerm, b: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::IntegerEqual(a.into(), b.into()), true)
    }

    #[test]
    fn integer_rewrite_presentation_accepts_only_the_same_normalized_claim() {
        let index = Bitvector32Term::Variable(Variable(9901));
        let value = IntegerTerm::from_machine(
            MachineIntegerType::UInt64,
            Bitvector32Term::Variable(Variable(9902)),
        )
        .unwrap();
        let other = IntegerTerm::from_machine(
            MachineIntegerType::UInt64,
            Bitvector32Term::Variable(Variable(9903)),
        )
        .unwrap();
        let observed = IntegerTerm::from_machine(MachineIntegerType::Int32, index.clone()).unwrap();
        let rhs = IntegerTerm::add(
            IntegerTerm::constant_i64(1),
            IntegerTerm::multiply(IntegerTerm::constant_i64(255), observed),
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::IntegerLessEqual(value.clone().into(), rhs.into()),
            true,
        );
        let cited = equality(index, Bitvector32Term::Constant(16));
        let facts = ProofFacts::default().with_fact(cited.clone());
        let mut rewrite = facts.check_equality_rewrite(&goal, &cited).unwrap();
        let raw = rewrite.proposition().clone();
        let folded = Proposition::ConditionIs(
            ConditionTerm::IntegerLessEqual(
                value.clone().into(),
                IntegerTerm::constant_i64(4081).into(),
            ),
            true,
        );
        assert_ne!(
            raw, folded,
            "substitution retains constant-expression structure"
        );
        let wrong_bound = Proposition::ConditionIs(
            ConditionTerm::IntegerLessEqual(
                value.clone().into(),
                IntegerTerm::constant_i64(4082).into(),
            ),
            true,
        );
        let wrong_atom = Proposition::ConditionIs(
            ConditionTerm::IntegerLessEqual(other.into(), IntegerTerm::constant_i64(4081).into()),
            true,
        );
        let wrong_relation = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(value.into(), IntegerTerm::constant_i64(4081).into()),
            true,
        );
        for forged in [wrong_bound, wrong_atom, wrong_relation] {
            assert!(!rewrite.try_present_as(&forged));
            assert_eq!(rewrite.proposition(), &raw);
        }
        assert!(rewrite.try_present_as(&folded));
        assert_eq!(rewrite.proposition(), &folded);
    }

    #[test]
    fn native_equality_rewrite_retains_folded_literal_widening() {
        let source = Bitvector32Term::Constant(u32::MAX);
        let replacement = Bitvector32Term::Variable(Variable(193_024));
        let value = Bitvector32Term::Variable(Variable(193_025));
        let cited = equality(source.clone(), replacement.clone());
        let facts = ProofFacts::default().with_fact(cited.clone());
        for (folded, lifted) in [
            (
                Bitvector32Term::Int64Constant(-1),
                Bitvector32Term::int64_from_32(replacement.clone()),
            ),
            (
                Bitvector32Term::Int64Constant(i64::from(u32::MAX)),
                Bitvector32Term::int64_from_uint32(replacement.clone()),
            ),
            (
                Bitvector32Term::UInt64Constant(u64::MAX),
                Bitvector32Term::uint64_from_int32(replacement.clone()),
            ),
            (
                Bitvector32Term::UInt64Constant(u64::from(u32::MAX)),
                Bitvector32Term::uint64_from_32(replacement.clone()),
            ),
        ] {
            let condition = |bound| {
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector64UnsignedLessThan(
                        Box::new(value.clone()),
                        Box::new(bound),
                    ),
                    true,
                )
            };
            assert_eq!(
                facts
                    .check_equality_rewrite(&condition(folded), &cited)
                    .unwrap()
                    .proposition(),
                &condition(lifted)
            );
        }
        // These full-width values have the same low bits as the source, but
        // no matching widening of it. The equality grants no substitution.
        for bound in [
            Bitvector32Term::UInt64Constant(0x1_ffff_ffff),
            Bitvector32Term::Int64Constant(0x1_ffff_ffff),
            Bitvector32Term::Int64Constant(-0x1_0000_0001),
        ] {
            let goal = Proposition::ConditionIs(
                ConditionTerm::Bitvector64UnsignedLessThan(
                    Box::new(value.clone()),
                    Box::new(bound),
                ),
                true,
            );
            assert!(facts.check_equality_rewrite(&goal, &cited).is_err());
        }
    }

    #[test]
    fn native_equality_rewrite_recovers_unsigned_32_bit_order_bias() {
        let value = Bitvector32Term::Variable(Variable(193_026));
        let divisor = Bitvector32Term::Variable(Variable(193_027));
        for source in [65521, 0x8000_0001, u32::MAX] {
            let source = Bitvector32Term::Constant(source);
            let cited = equality(source.clone(), divisor.clone());
            let facts = ProofFacts::default().with_fact(cited.clone());
            for make in [
                ConditionTerm::unsigned_less_than
                    as fn(Bitvector32Term, Bitvector32Term) -> ConditionTerm,
                ConditionTerm::unsigned_less_equal,
            ] {
                for truth in [false, true] {
                    let condition = make(value.clone(), source.clone());
                    if matches!(condition, ConditionTerm::Constant(_)) {
                        continue; // A fully folded bound contains no operand to rewrite.
                    }
                    let goal = Proposition::ConditionIs(condition, truth);
                    let expected =
                        Proposition::ConditionIs(make(value.clone(), divisor.clone()), truth);
                    assert_eq!(
                        facts
                            .check_equality_rewrite(&goal, &cited)
                            .unwrap()
                            .proposition(),
                        &expected
                    );
                    assert!(
                        ProofFacts::default()
                            .check_equality_rewrite(&goal, &cited)
                            .is_err()
                    );
                }
            }
        }
    }

    #[test]
    fn native_equality_rewrite_enters_integer_observation_bounds() {
        let x = Bitvector32Term::Variable(Variable(193_022));
        let y = Bitvector32Term::Variable(Variable(193_023));
        let cited = equality(x.clone(), y.clone());
        let observe = |value| IntegerTerm::from_machine(MachineIntegerType::UInt32, value).unwrap();
        let comparisons = [
            ConditionTerm::IntegerLessThan
                as fn(SharedIntegerTerm, SharedIntegerTerm) -> ConditionTerm,
            ConditionTerm::IntegerLessEqual,
            ConditionTerm::IntegerGreaterThan,
            ConditionTerm::IntegerGreaterEqual,
            ConditionTerm::IntegerNotEqual,
        ];
        for make in comparisons {
            let term =
                |value| IntegerTerm::add(observe(value), IntegerTerm::constant_i64(4294967295i64));
            for truth in [false, true] {
                let goal = Proposition::ConditionIs(
                    make(
                        term(x.clone()).into(),
                        IntegerTerm::constant_i64(8589934590i64).into(),
                    ),
                    truth,
                );
                let expected = Proposition::ConditionIs(
                    make(
                        term(y.clone()).into(),
                        IntegerTerm::constant_i64(8589934590i64).into(),
                    ),
                    truth,
                );
                let facts = ProofFacts::default().with_fact(cited.clone());
                assert_eq!(
                    facts
                        .check_equality_rewrite(&goal, &cited)
                        .unwrap()
                        .proposition(),
                    &expected
                );
                assert!(
                    ProofFacts::default()
                        .check_equality_rewrite(&goal, &cited)
                        .is_err()
                );
            }
        }
    }

    #[test]
    fn integer_equality_rewrite_checks_exact_authority_direction_and_compound_terms() {
        let x = IntegerTerm::var(Variable(193_001));
        let y = IntegerTerm::var(Variable(193_002));
        let z = IntegerTerm::var(Variable(193_003));
        let source = IntegerTerm::truncating_quotient(x.clone(), z.clone());
        let cited = integer_equality(source.clone(), y.clone());
        let compound = |a| IntegerTerm::add(IntegerTerm::multiply(a, z.clone()), x.clone());
        let goal = integer_equality(compound(source.clone()), z.clone());
        let expected = integer_equality(compound(y.clone()), z.clone());
        let empty = ProofFacts::default();
        assert!(empty.check_equality_rewrite(&goal, &cited).is_err());
        for evidence in [cited.clone(), integer_equality(y.clone(), source.clone())] {
            let facts = empty.with_fact(evidence);
            let mut checked = facts.check_equality_rewrite(&goal, &cited).unwrap();
            assert_eq!(checked.proposition(), &expected);
            assert!(!checked.try_present_as(&integer_equality(compound(y.clone()), x.clone())));
            assert_eq!(checked.proposition(), &expected);
            let reverse = integer_equality(y.clone(), source.clone());
            assert_eq!(
                facts
                    .check_equality_rewrite(&expected, &reverse)
                    .unwrap()
                    .proposition(),
                &goal
            );
            assert!(
                facts
                    .check_equality_rewrite(&integer_equality(x.clone(), z.clone()), &cited)
                    .is_err()
            );
        }
        let false_cited = Proposition::Not(Box::new(cited.clone()));
        assert!(
            empty
                .with_fact(false_cited.clone())
                .check_equality_rewrite(&goal, &false_cited)
                .is_err()
        );
        let mut false_polarity = cited.clone();
        if let Proposition::ConditionIs(_, truth) = &mut false_polarity {
            *truth = false;
        }
        assert!(
            empty
                .with_fact(false_polarity.clone())
                .check_equality_rewrite(&goal, &false_polarity)
                .is_err()
        );
        assert_eq!(
            empty
                .check_equality_rewrite(&goal, &integer_equality(x.clone(), x.clone()))
                .unwrap()
                .proposition(),
            &goal
        );
        // Substitution preserves relation polarity rather than proving its result.
        let negative = Proposition::Not(Box::new(goal));
        assert_eq!(
            empty
                .with_fact(cited.clone())
                .check_equality_rewrite(&negative, &cited)
                .unwrap()
                .proposition(),
            &Proposition::Not(Box::new(expected))
        );
    }

    #[test]
    fn integer_equality_rewrite_preserves_scopes_and_machine_carriers() {
        let x = IntegerTerm::var(Variable(193_011));
        let y = IntegerTerm::var(Variable(193_012));
        let cited = integer_equality(x.clone(), y.clone());
        let facts = ProofFacts::default().with_fact(cited.clone());
        let goal = integer_equality(IntegerTerm::multiply(x.clone(), x.clone()), y.clone());
        for variable in [Variable(193_011), Variable(193_012)] {
            let quantified = Proposition::ForAll {
                var: variable,
                sort: Sort::Integer,
                body: Box::new(goal.clone()),
            };
            assert!(facts.check_equality_rewrite(&quantified, &cited).is_err());
        }
        let unrelated = Proposition::ForAll {
            var: Variable(193_013),
            sort: Sort::Integer,
            body: Box::new(goal.clone()),
        };
        let expected = Proposition::ForAll {
            var: Variable(193_013),
            sort: Sort::Integer,
            body: Box::new(integer_equality(
                IntegerTerm::multiply(y.clone(), y.clone()),
                y.clone(),
            )),
        };
        assert_eq!(
            facts
                .check_equality_rewrite(&unrelated, &cited)
                .unwrap()
                .proposition(),
            &expected
        );
        let fold = IntegerTerm::range_fold(
            IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::constant_i64(2).into(),
            },
            IntegerTerm::constant_i64(0),
            Variable(193_012),
            Variable(193_014),
            x.clone(),
        );
        let refused =
            facts.check_equality_rewrite(&integer_equality(fold.clone(), y.clone()), &cited);
        assert!(
            refused
                .err()
                .unwrap()
                .contains("internal fold or match binder")
        );
        // A whole fold is still a valid exact occurrence: no binder is entered.
        let fold_cited = integer_equality(fold.clone(), y.clone());
        assert_eq!(
            facts
                .with_fact(fold_cited.clone())
                .check_equality_rewrite(&integer_equality(fold, x.clone()), &fold_cited)
                .unwrap()
                .proposition(),
            &integer_equality(y.clone(), x.clone())
        );
        for destination in [
            MachineIntegerType::Int32,
            MachineIntegerType::Int64,
            MachineIntegerType::Int128,
        ] {
            let cast = |value: IntegerTerm| {
                Term::Bitvector32(Bitvector32Term::IntegerToMachine {
                    value: value.into(),
                    destination,
                })
            };
            let native_goal = Proposition::Equal(cast(x.clone()), cast(y.clone()));
            assert_eq!(
                facts
                    .check_equality_rewrite(&native_goal, &cited)
                    .unwrap()
                    .proposition(),
                &Proposition::Equal(cast(y.clone()), cast(y.clone()))
            );
        }
        let application = |value: IntegerTerm| {
            IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                "opaque_integer".into(),
                vec![PureFunctionArgument::Integer(value.into())],
            ))
        };
        let application_goal = integer_equality(application(x.clone()), y.clone());
        assert_eq!(
            facts
                .check_equality_rewrite(&application_goal, &cited)
                .unwrap()
                .proposition(),
            &integer_equality(application(y.clone()), y.clone())
        );
        let expanded = IntegerTerm::add(x.clone(), x.clone());
        let self_reference = integer_equality(x.clone(), expanded.clone());
        assert_eq!(
            facts
                .with_fact(self_reference.clone())
                .check_equality_rewrite(&integer_equality(x.clone(), y.clone()), &self_reference)
                .unwrap()
                .proposition(),
            &integer_equality(expanded, y.clone())
        );
        // One bitvector carrier can be observed at several widths and signs.
        // Equalities between its int64 observations grant no cross-type match.
        let observe = |ty| {
            IntegerTerm::from_machine(ty, Bitvector32Term::Variable(Variable(193_015))).unwrap()
        };
        let wide = integer_equality(observe(MachineIntegerType::Int64), y.clone());
        for ty in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt64,
            MachineIntegerType::Int128,
        ] {
            let wrong_carrier =
                integer_equality(IntegerTerm::multiply(observe(ty), x.clone()), y.clone());
            assert!(
                facts
                    .with_fact(wide.clone())
                    .check_equality_rewrite(&wrong_carrier, &wide)
                    .is_err()
            );
        }
    }

    #[test]
    fn integer_equality_rewrite_keeps_snapshot_identity_and_checks_work_budget() {
        let _session = VerificationSession::enter();
        let pointer = Pointer {
            block: "integer-rewrite-snapshot".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = CMemory::new().with_block("integer-rewrite-snapshot", 8);
        let after = before.clone().store(
            pointer.clone(),
            CValue::Int64(Bitvector32Term::Int64Constant(9)),
        );
        let observe = |memory: CMemory| {
            IntegerTerm::from_machine(
                MachineIntegerType::Int64,
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(memory),
                    Box::new(pointer.clone()),
                    LoadKind::Bits64,
                ),
            )
            .unwrap()
        };
        let x = observe(before);
        let changed = observe(after);
        let y = IntegerTerm::var(Variable(193_031));
        let cited = integer_equality(x.clone(), y.clone());
        let facts = ProofFacts::default().with_fact(cited.clone());
        let compound = |a| integer_equality(IntegerTerm::multiply(a, y.clone()), y.clone());
        assert!(
            facts
                .check_equality_rewrite(&compound(changed), &cited)
                .is_err()
        );
        assert_eq!(
            facts
                .check_equality_rewrite(&compound(x.clone()), &cited)
                .unwrap()
                .proposition(),
            &compound(y.clone())
        );
        let limits = crate::instrumentation::TacticWorkLimits {
            simple: 0,
            smart: 0,
            control: 0,
        };
        let result = crate::instrumentation::with_tactic_work_limits(limits, || {
            crate::instrumentation::collect(|| {
                let tactic = crate::instrumentation::TacticEvent {
                    source_tactic_path: None,
                    claim: "Integer equality rewrite".into(),
                    tactic_index: 0,
                    tactic_name: "rewrite".into(),
                    class: "simple".into(),
                    statement_index: 0,
                    source_index: 0,
                };
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::TacticStarted(tactic.clone()),
                );
                let result = facts.check_equality_rewrite(&compound(x), &cited);
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::TacticFailed(tactic),
                );
                result.err().unwrap()
            })
            .0
        });
        assert!(result.contains("work budget"), "{result}");
    }

    #[test]
    fn integer_equality_rewrite_preserves_unrelated_native_observation_syntax() {
        let x = IntegerTerm::var(Variable(193_041));
        let y = IntegerTerm::var(Variable(193_042));
        let cited = integer_equality(x.clone(), y.clone());
        let facts = ProofFacts::default().with_fact(cited.clone());
        // These raw native forms are valid opaque observation identities.
        // Congruence must not fold them while rewriting an unrelated Integer.
        let terms = [
            Bitvector32Term::MachineIntegerCast {
                value: Box::new(Bitvector32Term::Constant(1)),
                source: MachineIntegerType::Int32,
                destination: MachineIntegerType::Int64,
            },
            Bitvector32Term::Int64FromUInt32(Box::new(Bitvector32Term::UInt32From64(Box::new(
                Bitvector32Term::UInt64Constant(1),
            )))),
            Bitvector32Term::If {
                condition: Box::new(ConditionTerm::Constant(true)),
                then_term: Box::new(Bitvector32Term::Int64Constant(1)),
                else_term: Box::new(Bitvector32Term::Int64Constant(2)),
            },
        ];
        for term in terms {
            let observed = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int64,
                Bitvector32Term::Int64Add(
                    Box::new(Bitvector32Term::Variable(Variable(193_043))),
                    Box::new(term),
                ),
            ));
            let goal = integer_equality(observed.clone(), IntegerTerm::add(x.clone(), x.clone()));
            let expected =
                integer_equality(observed.clone(), IntegerTerm::add(y.clone(), y.clone()));
            assert_eq!(
                facts
                    .check_equality_rewrite(&goal, &cited)
                    .unwrap()
                    .proposition(),
                &expected
            );
            assert!(
                facts
                    .check_equality_rewrite(&integer_equality(observed.clone(), observed), &cited)
                    .is_err()
            );
        }
        // A payload that actually contains the cited Integer still rewrites,
        // while its surrounding native cast remains an exact cast node.
        let cast = |value: IntegerTerm| {
            IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int64,
                Bitvector32Term::MachineIntegerCast {
                    value: Box::new(Bitvector32Term::IntegerToMachine {
                        value: value.into(),
                        destination: MachineIntegerType::Int32,
                    }),
                    source: MachineIntegerType::Int32,
                    destination: MachineIntegerType::Int64,
                },
            ))
        };
        assert_eq!(
            facts
                .check_equality_rewrite(&integer_equality(cast(x), y.clone()), &cited)
                .unwrap()
                .proposition(),
            &integer_equality(cast(y.clone()), y)
        );
    }

    #[test]
    fn checked_rewrite_requires_the_cited_equality_in_its_own_context() {
        let x = Bitvector32Term::Variable(Variable(901));
        let y = Bitvector32Term::Variable(Variable(902));
        let one = Bitvector32Term::Constant(1);
        let cited = equality(x.clone(), y.clone());
        let goal = equality(x.clone(), one.clone());
        let empty = ProofFacts::default();
        let established = empty.with_fact(cited.clone());
        let sibling = empty.with_fact(equality(y.clone(), one.clone()));
        assert!(empty.check_equality_rewrite(&goal, &cited).is_err());
        assert!(sibling.check_equality_rewrite(&goal, &cited).is_err());
        let result = established.check_equality_rewrite(&goal, &cited).unwrap();
        let (obligation, facts) = result.into_obligation((), None::<()>);
        assert_eq!(obligation.proposition(), &equality(y.clone(), one.clone()));
        assert!(facts.materialization_available(&cited));
        let reversed = ProofFacts::from_ordered(&[equality(y.clone(), x)]);
        let (obligation, _) = reversed
            .check_equality_rewrite(&goal, &cited)
            .unwrap()
            .into_obligation((), None::<()>);
        assert_eq!(obligation.proposition(), &equality(y, one));
    }

    #[test]
    fn checked_rewrite_rejects_forged_presentation_without_changing_result() {
        let x = Bitvector32Term::Variable(Variable(911));
        let y = Bitvector32Term::Variable(Variable(912));
        let cited = equality(x.clone(), y.clone());
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&cited));
        let goal = equality(x, Bitvector32Term::Constant(3));
        let expected = equality(y, Bitvector32Term::Constant(3));
        let mut result = facts.check_equality_rewrite(&goal, &cited).unwrap();
        let forged = equality(Bitvector32Term::Constant(0), Bitvector32Term::Constant(0));
        assert!(!result.try_present_as(&forged));
        assert!(result.try_present_as(&expected));
        let (obligation, retained) = result.into_obligation("display", None::<()>);
        assert_eq!(obligation.proposition(), &expected);
        assert!(retained.shares_premises_with(&facts));
    }

    // Both widths use the same corresponding-leaf checker. A write, a
    // different read kind, address, or operator cannot stand in for that leaf.
    #[test]
    fn compound_read_rewrite_checks_snapshots_kinds_and_operators() {
        let _session = crate::kernel::VerificationSession::enter();
        for wide in [false, true] {
            let pointer = Pointer {
                block: "compound-rewrite".into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let before = CMemory::new().with_block("compound-rewrite", 16);
            let after = before.clone().with_block("local:compound-unrelated", 4);
            let changed = after.clone().store(
                pointer.clone(),
                if wide {
                    CValue::UInt64(Bitvector32Term::UInt64Constant(7))
                } else {
                    CValue::Int32(Bitvector32Term::Constant(7))
                },
            );
            let kind = if wide {
                LoadKind::Bits64
            } else {
                LoadKind::Bits32
            };
            crate::kernel::eval::declare_load_access_width(&pointer, if wide { 8 } else { 4 });
            let load = |memory: &CMemory, pointer: Pointer, kind| {
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory_ref(memory),
                    Box::new(pointer),
                    kind,
                )
            };
            let one = if wide {
                Bitvector32Term::UInt64Constant(1)
            } else {
                Bitvector32Term::Constant(1)
            };
            let mask = |value| {
                if wide {
                    Bitvector32Term::UInt64BitwiseAnd(Box::new(value), Box::new(one.clone()))
                } else {
                    Bitvector32Term::BitwiseAnd(Box::new(value), Box::new(one.clone()))
                }
            };
            let eq = |a, b| {
                Proposition::ConditionIs(
                    if wide {
                        ConditionTerm::Bitvector64Equal(Box::new(a), Box::new(b))
                    } else {
                        ConditionTerm::equal(a, b)
                    },
                    true,
                )
            };
            let cited = eq(mask(load(&before, pointer.clone(), kind)), one.clone());
            let facts = ProofFacts::from_ordered(std::slice::from_ref(&cited));
            let goal = eq(mask(load(&after, pointer.clone(), kind)), one.clone());
            let checked = facts
                .check_equality_rewrite(&goal, &cited)
                .expect("unchanged selected cell");
            assert_eq!(
                checked.proposition(),
                &Proposition::ConditionIs(
                    if wide {
                        ConditionTerm::Bitvector64Equal(
                            Box::new(one.clone()),
                            Box::new(one.clone()),
                        )
                    } else {
                        ConditionTerm::Bitvector32Equal(
                            Box::new(one.clone()),
                            Box::new(one.clone()),
                        )
                    },
                    true
                )
            );
            assert!(
                ProofFacts::default()
                    .check_equality_rewrite(&goal, &cited)
                    .is_err()
            );
            for wrong in [
                mask(load(&changed, pointer.clone(), kind)),
                mask(load(
                    &after,
                    pointer.clone(),
                    if wide {
                        LoadKind::Bits32
                    } else {
                        LoadKind::Bits64
                    },
                )),
                mask(load(
                    &after,
                    Pointer {
                        offset: PointerOffsetTerm::Constant(8),
                        ..pointer.clone()
                    },
                    kind,
                )),
                if wide {
                    Bitvector32Term::UInt64BitwiseOr(
                        Box::new(load(&after, pointer.clone(), kind)),
                        Box::new(one.clone()),
                    )
                } else {
                    Bitvector32Term::BitwiseOr(
                        Box::new(load(&after, pointer.clone(), kind)),
                        Box::new(one.clone()),
                    )
                },
            ] {
                assert!(
                    facts
                        .check_equality_rewrite(&eq(wrong, one.clone()), &cited)
                        .is_err()
                );
            }
        }
    }

    #[test]
    fn compound_read_rewrite_work_is_local_to_selected_expressions() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer {
            block: "compound-rewrite-work".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        crate::kernel::eval::declare_load_access_width(&pointer, 8);
        let before = CMemory::new().with_block("compound-rewrite-work", 8);
        let after = before.clone().with_block("local:compound-rewrite-work", 4);
        let expression = |memory: &CMemory, size| {
            let mut term = Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory_ref(memory),
                Box::new(pointer.clone()),
                LoadKind::Bits64,
            );
            for index in 0..size {
                term = Bitvector32Term::UInt64BitwiseXor(
                    Box::new(term),
                    Box::new(Bitvector32Term::Variable(Variable(931_000 + index))),
                );
            }
            term
        };
        let eq = |a, b| {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector64Equal(Box::new(a), Box::new(b)),
                true,
            )
        };
        let mut costs = Vec::new();
        for size in [8, 32, 128] {
            let cited = eq(
                expression(&before, size),
                Bitvector32Term::UInt64Constant(1),
            );
            let goal = eq(expression(&after, size), Bitvector32Term::UInt64Constant(1));
            let mut context_costs = Vec::new();
            for ambient in [0, 32, 128] {
                let mut facts = ProofFacts::from_ordered(std::slice::from_ref(&cited));
                for i in 0..ambient {
                    facts = facts.with_fact(equality(
                        Bitvector32Term::Variable(Variable(930_000 + i)),
                        Bitvector32Term::Constant(i as u32),
                    ));
                }
                crate::kernel::eval::clear_load_canonicalization_caches();
                let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                    facts.check_equality_rewrite(&goal, &cited)
                });
                assert!(result.is_ok());
                context_costs.push(work);
            }
            assert!(
                context_costs.iter().all(|work| *work <= context_costs[0]),
                "{context_costs:?}"
            );
            costs.push(context_costs[0]);
        }
        assert!(
            costs.windows(2).all(|pair| pair[1] <= 4 * pair[0]),
            "{costs:?}"
        );
    }

    #[test]
    fn checked_rewrite_presentation_requires_checked_load_transport() {
        let pointer = Pointer {
            block: "rewrite-presentation".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        // The load is an `int32` one. A stored value answers only for a read
        // of its own width, and a load whose width nobody recorded is taken
        // as the widest scalar access, which no `int32` store supplies.
        crate::kernel::eval::declare_load_access_width(&pointer, 4);
        let memory = CMemory::new().with_block("rewrite-presentation", 4).store(
            pointer.clone(),
            CValue::Int32(Bitvector32Term::Constant(42)),
        );
        let changed = memory.clone().store(
            pointer.clone(),
            CValue::Int32(Bitvector32Term::Constant(43)),
        );
        let load = |memory| {
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(memory),
                Box::new(pointer.clone()),
                crate::kernel::LoadKind::Bits32,
            )
        };
        let x = Bitvector32Term::Variable(Variable(931));
        let y = Bitvector32Term::Variable(Variable(932));
        let cited = equality(x.clone(), y.clone());
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&cited));
        let mut result = facts
            .check_equality_rewrite(&equality(x, load(memory)), &cited)
            .unwrap();
        assert!(!result.try_present_as(&equality(y.clone(), load(changed))));
        assert!(result.try_present_as(&equality(y.clone(), Bitvector32Term::Constant(42))));
        let (obligation, _) = result.into_obligation((), None::<()>);
        assert_eq!(
            obligation.proposition(),
            &equality(y, Bitvector32Term::Constant(42))
        );
    }

    #[test]
    fn equality_rewrite_does_not_capture_or_replace_a_quantifier_binder() {
        fn checked_rewrite(
            goal: &Proposition,
            equality: &Proposition,
            available: &[Proposition],
        ) -> Result<Proposition, String> {
            ProofFacts::from_ordered(available)
                .check_equality_rewrite(goal, equality)
                .map(|checked| checked.proposition)
        }
        let bound = Variable(2_000_000);
        let free = Variable(71);
        let atom = |left, right| {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
                true,
            )
        };
        let variable = |id| Bitvector32Term::Variable(id);
        let quantified = |body| Proposition::ForAll {
            var: bound,
            sort: Sort::CInt32,
            body: Box::new(body),
        };

        let shadowed = atom(variable(bound), Bitvector32Term::Constant(0));
        let shadowed_goal = quantified(atom(variable(bound), Bitvector32Term::Constant(0)));
        assert!(
            checked_rewrite(&shadowed_goal, &shadowed, std::slice::from_ref(&shadowed),).is_err(),
            "an outer equality cannot replace the bound occurrence"
        );

        let capturing = atom(variable(free), variable(bound));
        let capturing_goal = quantified(atom(variable(free), Bitvector32Term::Constant(0)));
        assert!(
            checked_rewrite(
                &capturing_goal,
                &capturing,
                std::slice::from_ref(&capturing),
            )
            .is_err(),
            "the replacement's free variable cannot become bound"
        );
        let existential = Proposition::Exists {
            name: "witness".to_string(),
            var: bound,
            sort: Sort::CInt32,
            body: Box::new(atom(variable(free), Bitvector32Term::Constant(0))),
        };
        assert!(
            checked_rewrite(&existential, &capturing, std::slice::from_ref(&capturing),).is_err(),
            "existential binders obey the same capture rule"
        );

        let hidden_capture = atom(
            variable(free),
            Bitvector32Term::ClickFunctionApplication {
                name: "f".to_string(),
                arguments: vec![PureFunctionArgument::Value(CValue::Int32(variable(bound)))],
            },
        );
        assert!(
            checked_rewrite(
                &capturing_goal,
                &hidden_capture,
                std::slice::from_ref(&hidden_capture),
            )
            .is_err(),
            "a variable inside a pure-function argument must not become bound"
        );

        let safe = atom(variable(free), Bitvector32Term::Constant(0));
        assert_eq!(
            checked_rewrite(&capturing_goal, &safe, std::slice::from_ref(&safe),)
                .expect("an unrelated equality may still rewrite under the binder"),
            quantified(atom(
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(0),
            )),
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/equality_rewrite/tests.rs");
    }
}

#[cfg(test)]
mod wide_range_reader_tests {
    use super::*;
    // Both offset and scalar observation rewrites traverse native bounds
    // without changing their domain or replacing their high bits.
    #[test]
    fn wide_resource_bounds_survive_offset_and_scalar_rewriting() {
        let _session = crate::kernel::VerificationSession::enter();
        let offset = PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(984_700))),
            byte_width: 4,
        };
        let base = Pointer {
            block: crate::kernel::PointerBlock::Symbolic(Variable(984_701)),
            offset: offset.clone(),
        };
        let wide = CMemoryRange::new_wide(
            base,
            Bitvector32Term::UInt64Constant(0),
            Bitvector32Term::UInt64Constant(1 << 33),
            4,
        );
        let goal = Proposition::CResourceContains {
            parent: Box::new(CResource::Memory(wide.clone())),
            child: Box::new(CResource::Memory(wide.clone())),
        };
        let equality = Proposition::ConditionIs(
            ConditionTerm::PointerOffsetEqual(
                Box::new(offset),
                Box::new(PointerOffsetTerm::Constant(0)),
            ),
            true,
        );
        let rewritten = rewrite_atomic_proposition_by_exact_equality(&goal, &equality).unwrap();
        let (_, range) = rewritten.memory_containment().unwrap();
        assert_eq!(range.kind(), crate::kernel::RangeIndexKind::UInt64);
        assert_eq!(range.bound_terms(), wide.bound_terms());
        let scalar_eq = Proposition::ConditionIs(
            ConditionTerm::equal(Bitvector32Term::Variable(Variable(984_700)), 0u32.into()),
            true,
        );
        let rewritten = rewrite_atomic_proposition_by_exact_equality(&goal, &scalar_eq).unwrap();
        let (_, range) = rewritten.memory_containment().unwrap();
        assert_eq!(range.kind(), wide.kind());
        assert_eq!(range.bound_terms(), wide.bound_terms());
        assert_eq!(range.base().offset.as_const(), Some(0));
    }
}

#[cfg(test)]
mod wide_bound_equality_reader_tests {
    use super::*;

    #[test]
    fn wide_range_bound_substitution_requires_full_width_equality() {
        let _session = crate::kernel::VerificationSession::enter();
        let end = Bitvector32Term::Variable(Variable(985_900));
        let wide = CMemoryRange::new_wide(
            Pointer::symbolic(Variable(985_901)),
            Bitvector32Term::UInt64Constant(0),
            end.clone(),
            1,
        );
        let goal = Proposition::CResourceContains {
            parent: Box::new(CResource::Memory(wide.clone())),
            child: Box::new(CResource::Memory(wide.clone())),
        };
        // Equality of a low word cannot turn a full native endpoint into zero.
        let narrow = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(Box::new(end.clone()), Box::new(0u32.into())),
            true,
        );
        assert!(rewrite_atomic_proposition_by_exact_equality(&goal, &narrow).is_err());
        let high = Bitvector32Term::UInt64Constant(1 << 33);
        let full = Proposition::ConditionIs(ConditionTerm::uint64_equal(end, high.clone()), true);
        let rewritten = rewrite_atomic_proposition_by_exact_equality(&goal, &full).unwrap();
        let (_, range) = rewritten.memory_containment().unwrap();
        assert_eq!(range.kind(), wide.kind());
        assert_eq!(range.bound_terms().1, &high);
    }
}

#[cfg(test)]
mod numeric_address_annotation_tests {
    use super::*;

    fn check(p: Pointer, q: Pointer) {
        let class = crate::kernel::effective_type::CAccessClass::Struct(
            crate::kernel::effective_type::CStructClass::opaque("node"),
        );
        let observed = |pointer: &Pointer| {
            Bitvector32Term::object_pointer_address(pointer.clone(), Some(class.clone()))
        };
        let equality = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(observed(&p), observed(&q)),
            true,
        );
        let mask = |pointer: &Pointer| {
            Proposition::ConditionIs(
                ConditionTerm::uint64_equal(
                    Bitvector32Term::uint64_bitwise_and(
                        observed(pointer),
                        Bitvector32Term::UInt64Constant(1),
                    ),
                    Bitvector32Term::UInt64Constant(0),
                ),
                true,
            )
        };
        let goal = mask(&p);
        let expected = mask(&q);
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&equality));
        let checked = facts.check_equality_rewrite(&goal, &equality).unwrap();
        assert_eq!(checked.proposition(), &expected);
        assert_eq!(
            rewrite_proposition_by_exact_equality(
                &goal,
                &equality,
                std::slice::from_ref(&equality)
            )
            .unwrap(),
            expected
        );
        let nested = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                observed(&p),
                Bitvector32Term::uint64_add(
                    observed(&q),
                    Bitvector32Term::uint64_bitwise_and(
                        observed(&p),
                        Bitvector32Term::UInt64Constant(1),
                    ),
                ),
            ),
            true,
        );
        let masked = mask(&p);
        let mask_facts = ProofFacts::from_ordered(std::slice::from_ref(&masked));
        assert_eq!(
            mask_facts
                .check_equality_rewrite(&nested, &masked)
                .unwrap()
                .proposition(),
            &equality,
        );
        let left = CPointerValue::new(p.clone(), CType::Int32Pointer)
            .with_extent(Some(SubobjectExtent::constant(p, 4)));
        for width in [4, 8] {
            let right = CPointerValue::new(q.clone(), CType::Int32Pointer)
                .with_extent(Some(SubobjectExtent::constant(q.clone(), width)));
            assert!(
                !facts
                    .assumptions()
                    .pointer_designations_match(&left, &right)
            );
        }
    }
    #[test]
    fn address_equality_rewrites_canonical_alignment_masks_without_pointer_authority() {
        let _session = VerificationSession::enter();
        check(
            Pointer::symbolic(Variable(998_821)),
            Pointer::symbolic(Variable(998_822)),
        );
        check(
            Pointer::integer_address(Bitvector32Term::Variable(Variable(998_823))),
            Pointer::integer_address(Bitvector32Term::Variable(Variable(998_824))),
        );
    }
}
