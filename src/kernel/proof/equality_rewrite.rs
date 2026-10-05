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
                // The explicitly cited read may precede the goal's read of
                // the same cell. Select only the goal's two atomic operands;
                // retain and validate their checked snapshot/address bridge
                // before doing ordinary exact substitution.
                let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(from, to), true) =
                    equality
                else {
                    return Err(original_error);
                };
                let is_read = |term: &Bitvector32Term| {
                    matches!(term, Bitvector32Term::MemoryLoad(..))
                        || matches!(term, Bitvector32Term::Variable(variable) if crate::kernel::is_load_variable(variable))
                };
                if !is_read(from) {
                    return Err(original_error);
                }
                let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), _) =
                    goal
                else {
                    return Err(original_error);
                };
                for selected in [left, right] {
                    if !is_read(selected) || selected == from {
                        continue;
                    }
                    let adapted = Proposition::ConditionIs(
                        ConditionTerm::equal(selected.as_ref().clone(), to.as_ref().clone()),
                        true,
                    );
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

fn reverse_equality(equality: &Proposition) -> Option<Proposition> {
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
        Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(a, b), true) => {
            ConditionTerm::PointerOffsetEqual(b.clone(), a.clone())
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

fn rewrite_with_admitted_equality(
    goal: &Proposition,
    equality: &Proposition,
) -> Result<Proposition, String> {
    if equality_is_vacuous(equality) {
        return Ok(goal.clone());
    }
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
                    Err(message) if message.contains("does not occur in") => {
                        results.push((atomic.clone(), false));
                    }
                    Err(message) => return Err(message),
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

/// Rewrites every occurrence of a symbolic pointer by its proven-equal
/// form in a goal the structural pointer rewrite does not handle, such as a
/// 64-bit comparison over an address (`(uint64)p`). Only an equality whose left side is a whole
/// symbolic pointer (`p == q`, not `p + 4 == q`) qualifies; the rewrite then
/// replaces that pointer variable and composes any displacement at each
/// occurrence, which is exact term congruence bounded by the goal's size.
/// Reached only for a goal shape the structural rewrite does not handle at
/// all, so every goal it rewrites keeps its result.
fn pointer_variable_rewrite(
    goal: &Proposition,
    left: &Pointer,
    right: &Pointer,
) -> Option<Proposition> {
    let PointerBlock::Symbolic(variable) = left.block else {
        return None;
    };
    if left.offset != PointerOffsetTerm::Constant(0) {
        return None;
    }
    let rewritten =
        crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_variable(variable, right)
            .proposition(goal);
    (&rewritten != goal).then_some(rewritten)
}

fn rewrite_atomic_proposition_by_exact_equality(
    goal: &Proposition,
    equality: &Proposition,
) -> Result<Proposition, String> {
    fn rewrite_c_value(
        value: &CValue,
        rewrite_term: &impl Fn(&Bitvector32Term) -> Bitvector32Term,
        rewrite_pointer: &impl Fn(&Pointer) -> Pointer,
    ) -> CValue {
        match value {
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
            CValue::Pointer(pointer) => {
                let mut rewritten = pointer.clone();
                rewritten.replace_pointer(rewrite_pointer(pointer.pointer()));
                CValue::Pointer(rewritten)
            }
        }
    }

    fn rewrite_algebraic(
        term: &AlgebraicTerm,
        rewrite_term: &impl Fn(&Bitvector32Term) -> Bitvector32Term,
        rewrite_pointer: &impl Fn(&Pointer) -> Pointer,
    ) -> AlgebraicTerm {
        let node = match &term.node {
            AlgebraicTermNode::Variable(variable) => AlgebraicTermNode::Variable(*variable),
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

    if let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) = equality {
        let mut rewrite = super::term_rewrite::TermRewrite::new(left, right);
        let rewritten = match goal {
            Proposition::Equal(a, b) => Proposition::Equal(rewrite.term(a), rewrite.term(b)),
            Proposition::ConditionIs(c, expected) => {
                Proposition::ConditionIs(rewrite.condition(c), *expected)
            }
            _ => {
                return Err("`rewrite` algebraic equality does not occur in this goal".to_string());
            }
        };
        if rewrite.refusal().is_some() {
            // A refused scope or exhausted work leaves placeholders in the
            // walker's result; it is not a rewritten goal.
            return Err(
                "`rewrite` cannot substitute this equality through a binder in the current goal"
                    .to_string(),
            );
        }
        if !rewrite.changed {
            return Err("`rewrite` equality does not occur in the current goal".to_string());
        }
        return Ok(rewritten);
    }

    if let Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(left, right), true) = equality
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
                _ => offset.clone(),
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
            let binary = |left_term: &Bitvector32Term, right_term: &Bitvector32Term| {
                (
                    Box::new(rewrite_term_offset(left_term, left, right)),
                    Box::new(rewrite_term_offset(right_term, left, right)),
                )
            };
            match term {
                Bitvector32Term::MachineIntegerCast {
                    value,
                    source,
                    destination,
                } => Bitvector32Term::machine_integer_cast(
                    *source,
                    *destination,
                    rewrite_term_offset(value, left, right),
                ),

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
                Bitvector32Term::UnsignedDivide(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::UnsignedDivide(left, right)
                }
                Bitvector32Term::Remainder(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::Remainder(left, right)
                }
                Bitvector32Term::UnsignedRemainder(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::UnsignedRemainder(left, right)
                }
                Bitvector32Term::ShiftLeft(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::ShiftLeft(left, right)
                }
                Bitvector32Term::ArithmeticShiftRight(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::ArithmeticShiftRight(left, right)
                }
                Bitvector32Term::LogicalShiftRight(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::LogicalShiftRight(left, right)
                }
                Bitvector32Term::BitwiseAnd(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::BitwiseAnd(left, right)
                }
                Bitvector32Term::BitwiseOr(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::BitwiseOr(left, right)
                }
                Bitvector32Term::BitwiseXor(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::BitwiseXor(left, right)
                }
                Bitvector32Term::Int64From32(value) => {
                    Bitvector32Term::int64_from_32(rewrite_term_offset(value, left, right))
                }
                Bitvector32Term::UInt64From32(value) => {
                    Bitvector32Term::uint64_from_32(rewrite_term_offset(value, left, right))
                }
                Bitvector32Term::UInt32From64(value) => {
                    Bitvector32Term::uint32_from_64(rewrite_term_offset(value, left, right))
                }
                Bitvector32Term::Int64FromUInt32(value) => {
                    Bitvector32Term::int64_from_uint32(rewrite_term_offset(value, left, right))
                }
                Bitvector32Term::UInt64FromInt32(value) => {
                    Bitvector32Term::uint64_from_int32(rewrite_term_offset(value, left, right))
                }
                Bitvector32Term::UInt64FromInt64(value) => {
                    Bitvector32Term::uint64_from_int64(rewrite_term_offset(value, left, right))
                }
                Bitvector32Term::Int64Add(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::int64_add(*left, *right)
                }
                Bitvector32Term::Int64Subtract(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::int64_subtract(*left, *right)
                }
                Bitvector32Term::Int64Multiply(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::int64_multiply(*left, *right)
                }
                Bitvector32Term::Int64Divide(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::int64_divide(*left, *right)
                }
                Bitvector32Term::Int64Remainder(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::int64_remainder(*left, *right)
                }
                Bitvector32Term::Int64ShiftLeft(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::int64_shift_left(*left, *right)
                }
                Bitvector32Term::Int64ArithmeticShiftRight(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::int64_arithmetic_shift_right(*left, *right)
                }
                Bitvector32Term::Int64BitwiseAnd(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::int64_bitwise_and(*left, *right)
                }
                Bitvector32Term::Int64BitwiseOr(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::int64_bitwise_or(*left, *right)
                }
                Bitvector32Term::Int64BitwiseXor(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::int64_bitwise_xor(*left, *right)
                }
                Bitvector32Term::Int64BitwiseNot(value) => {
                    Bitvector32Term::int64_bitwise_not(rewrite_term_offset(value, left, right))
                }
                Bitvector32Term::UInt64Add(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::uint64_add(*left, *right)
                }
                Bitvector32Term::UInt64Subtract(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::uint64_subtract(*left, *right)
                }
                Bitvector32Term::UInt64Multiply(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::uint64_multiply(*left, *right)
                }
                Bitvector32Term::UInt64Divide(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::uint64_divide(*left, *right)
                }
                Bitvector32Term::UInt64Remainder(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::uint64_remainder(*left, *right)
                }
                Bitvector32Term::UInt64ShiftLeft(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::uint64_shift_left(*left, *right)
                }
                Bitvector32Term::UInt64LogicalShiftRight(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::uint64_logical_shift_right(*left, *right)
                }
                Bitvector32Term::UInt64BitwiseAnd(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::uint64_bitwise_and(*left, *right)
                }
                Bitvector32Term::UInt64BitwiseOr(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::uint64_bitwise_or(*left, *right)
                }
                Bitvector32Term::UInt64BitwiseXor(left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::uint64_bitwise_xor(*left, *right)
                }
                Bitvector32Term::UInt64BitwiseNot(value) => {
                    Bitvector32Term::uint64_bitwise_not(rewrite_term_offset(value, left, right))
                }
                Bitvector32Term::BitwiseNot(value) => {
                    Bitvector32Term::BitwiseNot(Box::new(rewrite_term_offset(value, left, right)))
                }
                Bitvector32Term::Float32Negate(value) => {
                    Bitvector32Term::float32_negate(rewrite_term_offset(value, left, right))
                }
                Bitvector32Term::Float32Binary {
                    operator,
                    left: left_term,
                    right: right_term,
                } => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::float32_binary(*left, *right, *operator)
                }
                Bitvector32Term::Float64Negate(value) => {
                    Bitvector32Term::float64_negate(rewrite_term_offset(value, left, right))
                }
                Bitvector32Term::Float64Binary {
                    operator,
                    left: left_term,
                    right: right_term,
                } => {
                    let (left, right) = binary(left_term, right_term);
                    Bitvector32Term::float64_binary(*left, *right, *operator)
                }
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
                Bitvector32Term::PointerAddress(pointer) => {
                    Bitvector32Term::PointerAddress(Box::new(rewrite_pointer(pointer)))
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
                    rewrite_term_offset(range.start(), left, right),
                    rewrite_term_offset(range.end(), left, right),
                )),
                CResource::Composite { .. }
                | CResource::Token { .. }
                | CResource::GuardedPopulation { .. }
                | CResource::PopulationAuthority(_)
                | CResource::Instance(_)
                | CResource::MutexGuard(_)
                | CResource::MutexLive(_)
                | CResource::MutexUse(_)
                | CResource::Iterated(_) => resource.clone(),
            }
        }
        let rewritten = match goal {
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
                    _ => {
                        return Err(
                            "`rewrite` pointer-offset equality does not occur in this goal"
                                .to_string(),
                        );
                    }
                };
                Proposition::ConditionIs(rewritten, *expected)
            }
            Proposition::CResourceSeparate {
                left: goal_left,
                right: goal_right,
            } => Proposition::CResourceSeparate {
                left: rewrite_resource_offset(goal_left, left, right),
                right: rewrite_resource_offset(goal_right, left, right),
            },
            Proposition::CResourceContains { parent, child } => Proposition::CResourceContains {
                parent: rewrite_resource_offset(parent, left, right),
                child: rewrite_resource_offset(child, left, right),
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
                return Err(
                    "`rewrite` pointer-offset equality does not occur in this goal".to_string(),
                );
            }
        };
        if &rewritten == goal {
            return Err("`rewrite` equality does not occur in the current goal".to_string());
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
                        return pointer_variable_rewrite(goal, left, right).ok_or_else(|| {
                            "`rewrite` pointer equality does not occur in this goal".to_string()
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
                return pointer_variable_rewrite(goal, left, right).ok_or_else(|| {
                    "`rewrite` pointer equality expects a condition goal".to_string()
                });
            }
        };
        if &rewritten == goal {
            return Err("`rewrite` equality does not occur in the current goal".to_string());
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
        _ => return Err("`rewrite` expects a 32-bit or 64-bit integer equality".to_string()),
    };
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
            // Load variables and load terms of one atom are the
            // same occurrence.
            || crate::kernel::terms_have_same_canonical_form(term, from)
        {
            return to.clone();
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
            Bitvector32Term::MachineIntegerCast {
                value,
                source,
                destination,
            } => Bitvector32Term::machine_integer_cast(
                *source,
                *destination,
                rewrite_term(value, from, to),
            ),

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
            Bitvector32Term::Divide(left, right) => {
                let (left, right) = binary(left, right);
                Bitvector32Term::Divide(left, right)
            }
            Bitvector32Term::UnsignedDivide(left, right) => {
                let (left, right) = binary(left, right);
                Bitvector32Term::UnsignedDivide(left, right)
            }
            Bitvector32Term::Remainder(left, right) => {
                let (left, right) = binary(left, right);
                Bitvector32Term::Remainder(left, right)
            }
            Bitvector32Term::UnsignedRemainder(left, right) => {
                let (left, right) = binary(left, right);
                Bitvector32Term::UnsignedRemainder(left, right)
            }
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
            Bitvector32Term::ArithmeticShiftRight(left, right) => {
                let (left, right) = binary(left, right);
                Bitvector32Term::ArithmeticShiftRight(left, right)
            }
            Bitvector32Term::LogicalShiftRight(left, right) => {
                let (left, right) = binary(left, right);
                Bitvector32Term::LogicalShiftRight(left, right)
            }
            Bitvector32Term::BitwiseAnd(left, right) => {
                let (left, right) = binary(left, right);
                Bitvector32Term::BitwiseAnd(left, right)
            }
            Bitvector32Term::BitwiseOr(left, right) => {
                let (left, right) = binary(left, right);
                Bitvector32Term::BitwiseOr(left, right)
            }
            Bitvector32Term::BitwiseXor(left, right) => {
                let (left, right) = binary(left, right);
                Bitvector32Term::BitwiseXor(left, right)
            }
            Bitvector32Term::Int64From32(value) => {
                Bitvector32Term::int64_from_32(rewrite_term(value, from, to))
            }
            Bitvector32Term::UInt64From32(value) => {
                Bitvector32Term::uint64_from_32(rewrite_term(value, from, to))
            }
            Bitvector32Term::UInt32From64(value) => {
                Bitvector32Term::uint32_from_64(rewrite_term(value, from, to))
            }
            Bitvector32Term::Int64FromUInt32(value) => {
                Bitvector32Term::int64_from_uint32(rewrite_term(value, from, to))
            }
            Bitvector32Term::UInt64FromInt32(value) => {
                Bitvector32Term::uint64_from_int32(rewrite_term(value, from, to))
            }
            Bitvector32Term::UInt64FromInt64(value) => {
                Bitvector32Term::uint64_from_int64(rewrite_term(value, from, to))
            }
            Bitvector32Term::Int64Add(left, right) => Bitvector32Term::int64_add(
                rewrite_term(left, from, to),
                rewrite_term(right, from, to),
            ),
            Bitvector32Term::Int64Subtract(left, right) => Bitvector32Term::int64_subtract(
                rewrite_term(left, from, to),
                rewrite_term(right, from, to),
            ),
            Bitvector32Term::Int64Multiply(left, right) => Bitvector32Term::int64_multiply(
                rewrite_term(left, from, to),
                rewrite_term(right, from, to),
            ),
            Bitvector32Term::Int64Divide(left, right) => Bitvector32Term::int64_divide(
                rewrite_term(left, from, to),
                rewrite_term(right, from, to),
            ),
            Bitvector32Term::Int64Remainder(left, right) => Bitvector32Term::int64_remainder(
                rewrite_term(left, from, to),
                rewrite_term(right, from, to),
            ),
            Bitvector32Term::Int64ShiftLeft(left, right) => Bitvector32Term::int64_shift_left(
                rewrite_term(left, from, to),
                rewrite_term(right, from, to),
            ),
            Bitvector32Term::Int64ArithmeticShiftRight(left, right) => {
                Bitvector32Term::int64_arithmetic_shift_right(
                    rewrite_term(left, from, to),
                    rewrite_term(right, from, to),
                )
            }
            Bitvector32Term::Int64BitwiseAnd(left, right) => Bitvector32Term::int64_bitwise_and(
                rewrite_term(left, from, to),
                rewrite_term(right, from, to),
            ),
            Bitvector32Term::Int64BitwiseOr(left, right) => Bitvector32Term::int64_bitwise_or(
                rewrite_term(left, from, to),
                rewrite_term(right, from, to),
            ),
            Bitvector32Term::Int64BitwiseXor(left, right) => Bitvector32Term::int64_bitwise_xor(
                rewrite_term(left, from, to),
                rewrite_term(right, from, to),
            ),
            Bitvector32Term::Int64BitwiseNot(value) => {
                Bitvector32Term::int64_bitwise_not(rewrite_term(value, from, to))
            }
            Bitvector32Term::UInt64Add(left, right) => Bitvector32Term::uint64_add(
                rewrite_term(left, from, to),
                rewrite_term(right, from, to),
            ),
            Bitvector32Term::UInt64Subtract(left, right) => Bitvector32Term::uint64_subtract(
                rewrite_term(left, from, to),
                rewrite_term(right, from, to),
            ),
            Bitvector32Term::UInt64Multiply(left, right) => Bitvector32Term::uint64_multiply(
                rewrite_term(left, from, to),
                rewrite_term(right, from, to),
            ),
            Bitvector32Term::UInt64Divide(left, right) => Bitvector32Term::uint64_divide(
                rewrite_term(left, from, to),
                rewrite_term(right, from, to),
            ),
            Bitvector32Term::UInt64Remainder(left, right) => Bitvector32Term::uint64_remainder(
                rewrite_term(left, from, to),
                rewrite_term(right, from, to),
            ),
            Bitvector32Term::UInt64ShiftLeft(left, right) => Bitvector32Term::uint64_shift_left(
                rewrite_term(left, from, to),
                rewrite_term(right, from, to),
            ),
            Bitvector32Term::UInt64LogicalShiftRight(left, right) => {
                Bitvector32Term::uint64_logical_shift_right(
                    rewrite_term(left, from, to),
                    rewrite_term(right, from, to),
                )
            }
            Bitvector32Term::UInt64BitwiseAnd(left, right) => Bitvector32Term::uint64_bitwise_and(
                rewrite_term(left, from, to),
                rewrite_term(right, from, to),
            ),
            Bitvector32Term::UInt64BitwiseOr(left, right) => Bitvector32Term::uint64_bitwise_or(
                rewrite_term(left, from, to),
                rewrite_term(right, from, to),
            ),
            Bitvector32Term::UInt64BitwiseXor(left, right) => Bitvector32Term::uint64_bitwise_xor(
                rewrite_term(left, from, to),
                rewrite_term(right, from, to),
            ),
            Bitvector32Term::UInt64BitwiseNot(value) => {
                Bitvector32Term::uint64_bitwise_not(rewrite_term(value, from, to))
            }
            Bitvector32Term::BitwiseNot(value) => {
                Bitvector32Term::BitwiseNot(Box::new(rewrite_term(value, from, to)))
            }
            Bitvector32Term::Float32Negate(value) => {
                Bitvector32Term::float32_negate(rewrite_term(value, from, to))
            }
            Bitvector32Term::Float32Binary {
                operator,
                left,
                right,
            } => {
                let (left, right) = binary(left, right);
                Bitvector32Term::float32_binary(*left, *right, *operator)
            }
            Bitvector32Term::Float64Negate(value) => {
                Bitvector32Term::float64_negate(rewrite_term(value, from, to))
            }
            Bitvector32Term::Float64Binary {
                operator,
                left,
                right,
            } => {
                let (left, right) = binary(left, right);
                Bitvector32Term::float64_binary(*left, *right, *operator)
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
            Bitvector32Term::PointerAddress(pointer) => {
                Bitvector32Term::PointerAddress(Box::new(Pointer {
                    block: pointer.block.clone(),
                    offset: rewrite_offset(&pointer.offset, from, to),
                }))
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
    // only root machine observations, scalar application arguments, and
    // Int32 range-fold endpoints are exposed, so Integer arithmetic has no new
    // rewrite/search path. Re-interning through `from_machine` also folds a
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
                IntegerTerm::PureFunctionApplication(SharedIntegerApplication::intern(
                    application.name().to_string(),
                    arguments,
                ))
                .into()
            }
            IntegerTerm::RangeFold {
                index: IntegerRangeFoldIndex::Int32 { start, end },
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
                    index: IntegerRangeFoldIndex::Int32 {
                        start: SharedIntegerRangeEndpoint::intern(rewritten_start),
                        end: SharedIntegerRangeEndpoint::intern(rewritten_end),
                    },
                    initial: initial.clone(),
                    accumulator: *accumulator,
                    item: *item,
                    body: body.clone(),
                }
                .into()
            }
            _ => term.clone(),
        }
    }

    let rewrite_resource_term = |resource: &CResource| match resource {
        CResource::Memory(range) => CResource::Memory(range.with_bounds(
            Pointer {
                block: range.base().block.clone(),
                offset: rewrite_offset_term(&range.base().offset, left, right),
            },
            rewrite_term(range.start(), left, right),
            rewrite_term(range.end(), left, right),
        )),
        CResource::Composite { .. }
        | CResource::Token { .. }
        | CResource::GuardedPopulation { .. }
        | CResource::PopulationAuthority(_)
        | CResource::Instance(_)
        | CResource::MutexGuard(_)
        | CResource::MutexLive(_)
        | CResource::MutexUse(_)
        | CResource::Iterated(_) => resource.clone(),
    };
    let rewritten = match goal {
        Proposition::ConditionIs(condition, expected) => {
            let rewritten_condition = match condition {
                ConditionTerm::Bitvector32SignedLessThan(goal_left, goal_right) => {
                    ConditionTerm::Bitvector32SignedLessThan(
                        Box::new(rewrite_term(goal_left, left, right)),
                        Box::new(rewrite_term(goal_right, left, right)),
                    )
                }
                ConditionTerm::Bitvector32SignedLessEqual(goal_left, goal_right) => {
                    ConditionTerm::Bitvector32SignedLessEqual(
                        Box::new(rewrite_term(goal_left, left, right)),
                        Box::new(rewrite_term(goal_right, left, right)),
                    )
                }
                ConditionTerm::Bitvector32SignedGreaterThan(goal_left, goal_right) => {
                    ConditionTerm::Bitvector32SignedGreaterThan(
                        Box::new(rewrite_term(goal_left, left, right)),
                        Box::new(rewrite_term(goal_right, left, right)),
                    )
                }
                ConditionTerm::Bitvector32SignedGreaterEqual(goal_left, goal_right) => {
                    ConditionTerm::Bitvector32SignedGreaterEqual(
                        Box::new(rewrite_term(goal_left, left, right)),
                        Box::new(rewrite_term(goal_right, left, right)),
                    )
                }
                ConditionTerm::Bitvector32Equal(goal_left, goal_right) => {
                    ConditionTerm::Bitvector32Equal(
                        Box::new(rewrite_term(goal_left, left, right)),
                        Box::new(rewrite_term(goal_right, left, right)),
                    )
                }
                ConditionTerm::Bitvector64Equal(goal_left, goal_right) => {
                    ConditionTerm::Bitvector64Equal(
                        Box::new(rewrite_term(goal_left, left, right)),
                        Box::new(rewrite_term(goal_right, left, right)),
                    )
                }
                ConditionTerm::Bitvector32SignedAddOverflows(goal_left, goal_right) => {
                    ConditionTerm::Bitvector32SignedAddOverflows(
                        Box::new(rewrite_term(goal_left, left, right)),
                        Box::new(rewrite_term(goal_right, left, right)),
                    )
                }
                ConditionTerm::Bitvector32SignedSubtractOverflows(goal_left, goal_right) => {
                    ConditionTerm::Bitvector32SignedSubtractOverflows(
                        Box::new(rewrite_term(goal_left, left, right)),
                        Box::new(rewrite_term(goal_right, left, right)),
                    )
                }
                ConditionTerm::Bitvector32SignedMultiplyOverflows(goal_left, goal_right) => {
                    ConditionTerm::Bitvector32SignedMultiplyOverflows(
                        Box::new(rewrite_term(goal_left, left, right)),
                        Box::new(rewrite_term(goal_right, left, right)),
                    )
                }
                ConditionTerm::Bitvector32SignedDivideOverflows(goal_left, goal_right) => {
                    ConditionTerm::Bitvector32SignedDivideOverflows(
                        Box::new(rewrite_term(goal_left, left, right)),
                        Box::new(rewrite_term(goal_right, left, right)),
                    )
                }
                ConditionTerm::Bitvector32SignedShiftLeftOverflows(goal_left, goal_right) => {
                    ConditionTerm::Bitvector32SignedShiftLeftOverflows(
                        Box::new(rewrite_term(goal_left, left, right)),
                        Box::new(rewrite_term(goal_right, left, right)),
                    )
                }
                ConditionTerm::Bitvector64SignedAddOverflows(goal_left, goal_right) => {
                    ConditionTerm::Bitvector64SignedAddOverflows(
                        Box::new(rewrite_term(goal_left, left, right)),
                        Box::new(rewrite_term(goal_right, left, right)),
                    )
                }
                ConditionTerm::Bitvector64SignedSubtractOverflows(goal_left, goal_right) => {
                    ConditionTerm::Bitvector64SignedSubtractOverflows(
                        Box::new(rewrite_term(goal_left, left, right)),
                        Box::new(rewrite_term(goal_right, left, right)),
                    )
                }
                ConditionTerm::Bitvector64SignedMultiplyOverflows(goal_left, goal_right) => {
                    ConditionTerm::Bitvector64SignedMultiplyOverflows(
                        Box::new(rewrite_term(goal_left, left, right)),
                        Box::new(rewrite_term(goal_right, left, right)),
                    )
                }
                ConditionTerm::Bitvector64SignedDivideOverflows(goal_left, goal_right) => {
                    ConditionTerm::Bitvector64SignedDivideOverflows(
                        Box::new(rewrite_term(goal_left, left, right)),
                        Box::new(rewrite_term(goal_right, left, right)),
                    )
                }
                ConditionTerm::Bitvector64SignedShiftLeftOverflows(goal_left, goal_right) => {
                    ConditionTerm::Bitvector64SignedShiftLeftOverflows(
                        Box::new(rewrite_term(goal_left, left, right)),
                        Box::new(rewrite_term(goal_right, left, right)),
                    )
                }
                // `to_integer(machine)` is represented as an Integer machine
                // observation.  Rewrite its selected machine payload through
                // the already checked C equality, then let the normal
                // Integer constructor fold a constant observation.
                ConditionTerm::IntegerEqual(goal_left, goal_right) => ConditionTerm::IntegerEqual(
                    rewrite_integer_observation(goal_left, left, right),
                    rewrite_integer_observation(goal_right, left, right),
                ),
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
                    return Err("`rewrite` currently expects an int32 comparison goal".to_string());
                }
            };
            Proposition::ConditionIs(rewritten_condition, *expected)
        }
        Proposition::CResourceSeparate {
            left: goal_left,
            right: goal_right,
        } => Proposition::CResourceSeparate {
            left: rewrite_resource_term(goal_left),
            right: rewrite_resource_term(goal_right),
        },
        Proposition::CResourceContains { parent, child } => Proposition::CResourceContains {
            parent: rewrite_resource_term(parent),
            child: rewrite_resource_term(child),
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
        } => Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: Pointer {
                block: base.block.clone(),
                offset: rewrite_offset_term(&base.offset, left, right),
            },
            bytes: rewrite_term(bytes, left, right),
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
        _ => return Err("`rewrite` int32 equality does not occur in this goal".to_string()),
    };
    if &rewritten == goal {
        return Err("`rewrite` equality does not occur in the current goal".to_string());
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
    fn cited_read_rewrite_requires_unchanged_cells_and_its_named_premise() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer {
            block: "rewrite-selected-read".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        crate::kernel::eval::declare_load_access_width(&pointer, 4);
        let before = CMemory::new().with_block("rewrite-selected-read", 4);
        let after = before.clone().with_block("local:rewrite-unrelated", 4);
        let changed = after.clone().store(
            pointer.clone(),
            CValue::Int32(Bitvector32Term::Constant(43)),
        );
        let load = |memory: &CMemory| {
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory_ref(memory),
                Box::new(pointer.clone()),
                crate::kernel::LoadKind::Bits32,
            )
        };
        let premise = equality(load(&before), Bitvector32Term::Constant(42));
        let goal = equality(load(&after), Bitvector32Term::Constant(42));
        let mut costs = vec![];
        for size in [16u64, 64, 256, 1024] {
            let mut facts = ProofFacts::from_ordered(std::slice::from_ref(&premise));
            for index in 0..size {
                facts = facts.with_fact(equality(
                    Bitvector32Term::Variable(Variable(80_000 + index)),
                    Bitvector32Term::Constant(index as u32),
                ));
            }
            crate::kernel::eval::clear_load_canonicalization_caches();
            let (rewritten, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.check_equality_rewrite(&goal, &premise)
            });
            assert_eq!(
                rewritten.unwrap().proposition(),
                &equality(Bitvector32Term::Constant(42), Bitvector32Term::Constant(42))
            );
            assert!(
                facts
                    .check_equality_rewrite(
                        &equality(load(&changed), Bitvector32Term::Constant(42)),
                        &premise
                    )
                    .is_err()
            );
            costs.push(work);
        }
        assert!(costs.iter().all(|work| *work <= 8), "{costs:?}");
        assert!(
            ProofFacts::default()
                .check_equality_rewrite(&goal, &premise)
                .is_err()
        );
    }

    #[test]
    fn checked_rewrite_does_not_scan_or_rebuild_ambient_facts() {
        let x = Bitvector32Term::Variable(Variable(921));
        let cited = equality(x.clone(), Bitvector32Term::Constant(7));
        let goal = equality(x, Bitvector32Term::Constant(9));
        let mut costs = Vec::new();
        for size in [16u64, 64, 256, 1024] {
            let mut facts = ProofFacts::default();
            for index in 0..size {
                facts = facts.with_fact(equality(
                    Bitvector32Term::Variable(Variable(10_000 + index)),
                    Bitvector32Term::Constant(index as u32),
                ));
            }
            facts = facts.with_fact(cited.clone());
            super::super::take_fact_entry_counts();
            let (_, cost) = crate::instrumentation::measure_deterministic_work(|| {
                facts.check_equality_rewrite(&goal, &cited).unwrap()
            });
            assert_eq!(super::super::take_fact_entry_counts(), (0, 0));
            costs.push(cost);
        }
        assert!(costs[0] > 0);
        assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
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

    #[test]
    fn rewrite_capture_collection_does_not_visit_snapshot_contents() {
        let free = Variable(41);
        let address = Variable(42);
        let mut costs = Vec::new();
        for size in [16u64, 64, 256, 1024] {
            let mut memory = CMemory::new();
            for i in 0..size {
                memory = memory.store(
                    Pointer::symbolic(Variable(100_000 + i)),
                    CValue::Int32(Bitvector32Term::Variable(Variable(200_000 + i))),
                );
            }
            let equality = Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(Bitvector32Term::Variable(free)),
                    Box::new(Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(memory),
                        Box::new(Pointer::symbolic(address)),
                        crate::kernel::LoadKind::Bits32,
                    )),
                ),
                true,
            );
            let (variables, work) = crate::instrumentation::measure_deterministic_work(|| {
                rewrite_equality_variables(&equality).unwrap()
            });
            assert_eq!(variables, BTreeSet::from([free, address]));
            costs.push(work);
        }
        assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
    }
    #[test]
    fn rewrite_integer_application_endpoint_keeps_byte_snapshot_and_ignores_its_contents() {
        let index = Bitvector32Term::Variable(Variable(47));
        let replacement = Bitvector32Term::Constant(9);
        let equality = Proposition::ConditionIs(
            ConditionTerm::equal(index.clone(), replacement.clone()),
            true,
        );
        let mut costs = Vec::new();
        for size in [16u64, 64, 256, 1024] {
            let mut memory = CMemory::new();
            for i in 0..size {
                memory = memory.store(
                    Pointer::symbolic(Variable(300000 + i)),
                    CValue::Int32(Bitvector32Term::Constant(i as u32)),
                );
            }
            let array = PureFunctionArgument::ArrayRef {
                memory,
                pointer: CValue::typed_pointer(
                    Pointer::symbolic(Variable(48)),
                    CType::UInt8Pointer,
                ),
                element_type: CType::UInt8,
            };
            let application = |endpoint| {
                IntegerTerm::PureFunctionApplication(SharedIntegerApplication::intern(
                    "prefix".into(),
                    vec![
                        array.clone(),
                        PureFunctionArgument::Value(CValue::Int32(endpoint)),
                    ],
                ))
            };
            let goal = Proposition::ConditionIs(
                ConditionTerm::integer_equal(
                    application(index.clone()),
                    application(replacement.clone()),
                ),
                true,
            );
            let expected = Proposition::ConditionIs(
                ConditionTerm::integer_equal(
                    application(replacement.clone()),
                    application(replacement.clone()),
                ),
                true,
            );
            let facts = ProofFacts::from_ordered(std::slice::from_ref(&equality));
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts
                    .check_equality_rewrite(&goal, &equality)
                    .map(|checked| checked.proposition().clone())
            });
            assert_eq!(result.unwrap(), expected);
            costs.push(work);
        }
        assert!(
            costs[0] > 0 && costs.iter().all(|work| *work == costs[0]),
            "{costs:?}"
        );
    }
}
