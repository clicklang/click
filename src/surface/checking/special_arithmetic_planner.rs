//! Bounded planning for pointer, finite-float, and native arithmetic facts.
//! Plans expand into ordinary library applications and normalization.

use super::*;
use crate::kernel::MachineBinaryOp;
#[cfg(test)]
use crate::kernel::binary_node;
use crate::kernel::binary_term;
use crate::kernel::cast_term;
use crate::kernel::proof::arithmetic_special::{
    SpecialArithmeticNode as KernelNode, SpecialArithmeticPlan as KernelPlan, float_bound_weakens,
    is_float_bound, signed_constant_bound_on_view, signed_definedness_query,
};
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{FloatClassification, FloatCondition, OldConditionTerm, Proposition};
use crate::kernel::{OffsetTree as _, OffsetView};
use crate::kernel::{
    bits32_constant, constant_i64, constant_u32, constant_u64, int64_constant, uint64_constant,
};
use crate::surface::{SpecialArithmeticNode, SpecializedCompositionPlan};

pub(super) fn plan_special_arithmetic(
    goal: &Proposition,
    premises: &[Proposition],
) -> Option<KernelPlan> {
    if !charge_proposition(goal) {
        return None;
    }
    if let Proposition::ConditionIs(condition, value) = goal
        && crate::kernel::PureFactContext::new()
            .widened_unsigned_sum_bound_premises(condition.old_form())
            .is_some()
    {
        let context = premises
            .iter()
            .fold(crate::kernel::PureFactContext::new(), |context, premise| {
                context.assume_proposition(premise.clone())
            });
        if context.decide_widened_sum_bound(condition.old_form()) == Some(*value) {
            return Some(KernelPlan {
                nodes: vec![KernelNode::UnsignedSumBound {
                    bounds: (0..premises.len()).collect(),
                    result: goal.clone(),
                }],
                conclusion: 0,
            });
        }
    }
    // `defined(a + b)` or `defined(a - b)` over `int32` or `int64`: cite
    // exactly the listed premises that bound an operand by a constant of
    // the goal's width. The kernel recomputes the operand ranges and
    // refuses a result that can leave that width.
    if let Some((width, operands, _)) = signed_definedness_query(goal) {
        let bounds = premises
            .iter()
            .enumerate()
            .filter_map(|(i, p)| {
                (charge_proposition(p)
                    && (signed_constant_bound_on_view(width, p, operands[0].operand_view())
                        .is_some()
                        || signed_constant_bound_on_view(width, p, operands[1].operand_view())
                            .is_some()))
                .then_some(i)
            })
            .collect();
        return Some(KernelPlan {
            nodes: vec![KernelNode::SignedDefined {
                width,
                bounds,
                result: goal.clone(),
            }],
            conclusion: 0,
        });
    }
    if is_float_bound(goal)
        && let Some(premise) = premises
            .iter()
            .position(|premise| charge_proposition(premise) && float_bound_weakens(premise, goal))
    {
        return Some(KernelPlan {
            nodes: vec![KernelNode::FloatBound {
                premise,
                result: goal.clone(),
            }],
            conclusion: 0,
        });
    }
    if let Some(finite) = float_finite_premise(goal, premises) {
        return Some(KernelPlan {
            nodes: vec![KernelNode::FloatReflexive {
                finite,
                result: goal.clone(),
            }],
            conclusion: 0,
        });
    }
    if is_alignment_goal(goal) {
        return Some(KernelPlan {
            nodes: vec![KernelNode::PointerAlignment {
                premise: premises
                    .iter()
                    .position(|p| charge_proposition(p) && is_positive_alignment(p)),
                result: goal.clone(),
            }],
            conclusion: 0,
        });
    }
    if is_pointer_relation(goal)
        && let Some(relation) = premises
            .iter()
            .position(|p| charge_proposition(p) && is_pointer_relation(p))
    {
        let bounds = premises
            .iter()
            .enumerate()
            .filter_map(|(i, p)| {
                (i != relation && charge_proposition(p) && is_pointer_translation_bound(p))
                    .then_some(i)
            })
            .collect();
        return Some(KernelPlan {
            nodes: vec![KernelNode::PointerTranslation {
                relation,
                bounds,
                result: goal.clone(),
            }],
            conclusion: 0,
        });
    }
    if is_bitvector64_equality(goal)
        && let Some(relation) = premises
            .iter()
            .position(|p| charge_proposition(p) && is_word_equality(p))
    {
        let alignments: Vec<usize> = premises
            .iter()
            .enumerate()
            .filter_map(|(i, p)| {
                (i != relation
                    && charge_proposition(p)
                    && is_positive_alignment(p)
                    && alignment_is_relevant(p, &premises[relation], goal))
                .then_some(i)
            })
            .collect();
        if !alignments.is_empty() {
            return Some(KernelPlan {
                nodes: vec![KernelNode::PointerWordEquality {
                    relation,
                    alignments,
                    result: goal.clone(),
                }],
                conclusion: 0,
            });
        }
    }
    if let Some(bounds) = cast_identity_bounds(goal, premises) {
        return Some(KernelPlan {
            nodes: vec![KernelNode::IntegerCastIdentity {
                bounds,
                result: goal.clone(),
            }],
            conclusion: 0,
        });
    }
    if is_bitvector64_goal(goal) {
        let alignments = premises
            .iter()
            .enumerate()
            .filter_map(|(i, p)| {
                (charge_proposition(p)
                    && is_positive_alignment(p)
                    && alignment_is_relevant(p, goal, goal))
                .then_some(i)
            })
            .collect::<Vec<_>>();
        if !alignments.is_empty() {
            return Some(KernelPlan {
                nodes: vec![KernelNode::PointerWordFromAlignment {
                    alignments,
                    result: goal.clone(),
                }],
                conclusion: 0,
            });
        }
    }
    None
}

pub(in crate::surface) fn special_plan_to_surface(
    plan: &KernelPlan,
    premises: &[SyntaxProposition],
    goal: &SyntaxProposition,
) -> SpecializedCompositionPlan {
    let nodes = plan
        .nodes
        .iter()
        .map(|node| match node {
            KernelNode::PointerTranslation {
                relation, bounds, ..
            } => SpecialArithmeticNode::PointerTranslation {
                relation: *relation,
                bounds: bounds.clone(),
                result: goal.clone(),
            },
            KernelNode::PointerAlignment { premise, .. } => {
                SpecialArithmeticNode::PointerAlignment {
                    premise: *premise,
                    result: goal.clone(),
                }
            }
            KernelNode::PointerWordEquality {
                relation,
                alignments,
                ..
            } => SpecialArithmeticNode::PointerWordEquality {
                relation: *relation,
                alignments: alignments.clone(),
                result: goal.clone(),
            },
            KernelNode::PointerWordFromAlignment { alignments, .. } => {
                SpecialArithmeticNode::PointerWordFromAlignment {
                    alignments: alignments.clone(),
                    result: goal.clone(),
                }
            }
            KernelNode::FloatBound { premise, .. } => SpecialArithmeticNode::FloatBound {
                premise: *premise,
                result: goal.clone(),
            },
            KernelNode::FloatReflexive { finite, .. } => SpecialArithmeticNode::FloatReflexive {
                finite: *finite,
                result: goal.clone(),
            },
            KernelNode::UnsignedSumBound { bounds, .. } => {
                SpecialArithmeticNode::UnsignedSumBound {
                    bounds: bounds.clone(),
                    result: goal.clone(),
                }
            }
            KernelNode::IntegerCastIdentity { bounds, .. } => {
                SpecialArithmeticNode::IntegerCastIdentity {
                    bounds: bounds.clone(),
                    result: goal.clone(),
                }
            }

            KernelNode::SignedDefined { width, bounds, .. } => {
                SpecialArithmeticNode::SignedDefined {
                    width: *width,
                    bounds: bounds.clone(),
                    result: goal.clone(),
                }
            }
        })
        .collect();
    let (premises, nodes) = cited_premises_only(premises, nodes);
    SpecializedCompositionPlan {
        premises,
        nodes,
        conclusion: plan.conclusion,
    }
}

/// The premise indices a node cites, for renumbering.
fn cited_premise_indices(node: &mut SpecialArithmeticNode) -> Vec<&mut usize> {
    match node {
        SpecialArithmeticNode::IntegerPolynomialIdentity { bounds, .. }
        | SpecialArithmeticNode::IntegerCastIdentity { bounds, .. }
        | SpecialArithmeticNode::UnsignedSumBound { bounds, .. }
        | SpecialArithmeticNode::SignedDefined { bounds, .. } => bounds.iter_mut().collect(),
        SpecialArithmeticNode::PointerTranslation {
            relation, bounds, ..
        } => std::iter::once(relation).chain(bounds.iter_mut()).collect(),
        SpecialArithmeticNode::PointerAlignment { premise, .. } => premise.iter_mut().collect(),
        SpecialArithmeticNode::PointerWordEquality {
            relation,
            alignments,
            ..
        } => std::iter::once(relation)
            .chain(alignments.iter_mut())
            .collect(),
        SpecialArithmeticNode::PointerWordFromAlignment { alignments, .. } => {
            alignments.iter_mut().collect()
        }
        SpecialArithmeticNode::FloatReflexive { finite, .. }
        | SpecialArithmeticNode::FloatBound {
            premise: finite, ..
        } => vec![finite],
    }
}

/// The certificate's premises narrowed to those its nodes cite, in their
/// original order, with the nodes renumbered to match. The planner offers
/// every candidate fact; a certificate that listed the unused ones would
/// require each to be exactly available again when it is rechecked, though
/// the proof never depends on them.
fn cited_premises_only(
    premises: &[SyntaxProposition],
    mut nodes: Vec<SpecialArithmeticNode>,
) -> (Vec<SyntaxProposition>, Vec<SpecialArithmeticNode>) {
    let mut cited = vec![false; premises.len()];
    for node in &mut nodes {
        for index in cited_premise_indices(node) {
            if let Some(flag) = cited.get_mut(*index) {
                *flag = true;
            }
        }
    }
    let mut renumbered = vec![None; premises.len()];
    let mut kept = Vec::new();
    for (index, premise) in premises.iter().enumerate() {
        if cited[index] {
            renumbered[index] = Some(kept.len());
            kept.push(premise.clone());
        }
    }
    for node in &mut nodes {
        for index in cited_premise_indices(node) {
            if let Some(Some(new)) = renumbered.get(*index) {
                *index = *new;
            }
        }
    }
    (kept, nodes)
}

/// For a goal `to_integer((T)x) == to_integer(x)`, either side first, the
/// first premises `lo <= to_integer(x)` and `to_integer(x) <= hi`, as written
/// or as a native comparison's Integer reading, with constant endpoints
/// inside `T`'s range. A widening of a narrow binder `x` instead cites the
/// range facts `x`'s introduction filed, matched exactly as filed.
fn cast_identity_bounds(goal: &Proposition, premises: &[Proposition]) -> Option<Vec<usize>> {
    use crate::kernel::IntegerTerm;
    use crate::kernel::machine_integer::conversion::{cast_operands, narrow_widening};
    let Some((OldConditionTerm::IntegerEqual(a, b), true)) = goal.old_condition() else {
        return None;
    };
    let (observed, original): (&IntegerTerm, &IntegerTerm) = [(a, b), (b, a)]
        .into_iter()
        .map(|(observed, original)| (observed.as_ref(), original.as_ref()))
        .find(|(observed, original)| {
            narrow_widening(observed, original) || cast_operands(observed).contains(original)
        })?;
    // The identity's destination is the format of the observation's value
    // reading (rule W), as `integer_cast_identity` checks it.
    let IntegerTerm::Machine(machine) = observed.value_read() else {
        return None;
    };
    let (min, max) = machine.ty().format().bounds();
    let bound = |lower: bool| {
        premises.iter().position(|premise| {
            // A bound with an exact native spelling is filed natively, as
            // `x <= 4294967295u64`; its Integer reading is the bound.
            let readings =
                crate::kernel::machine_integer::comparison::integer_observations_of_native_comparison(premise);
            std::iter::once(premise).chain(&readings).any(|reading| {
                let Some((OldConditionTerm::IntegerLessEqual(left, right), true)) = reading.old_condition() else {
                    return false;
                };
                let (endpoint, operand) = if lower { (left, right) } else { (right, left) };
                operand.as_ref() == original
                    && endpoint.as_const().is_some_and(|endpoint| {
                        if lower {
                            endpoint >= &min
                        } else {
                            endpoint <= &max
                        }
                    })
            })
        })
    };
    Some(vec![bound(true)?, bound(false)?])
}

fn is_positive_alignment(p: &Proposition) -> bool {
    matches!(p, Proposition::ConditionIs(condition, true) if alignment_shape(condition.old_form()).is_some())
}

fn alignment_is_relevant(
    alignment: &Proposition,
    relation: &Proposition,
    goal: &Proposition,
) -> bool {
    let Proposition::ConditionIs(condition, true) = alignment else {
        return false;
    };
    let Some((pointer, _)) = alignment_shape(condition.old_form()) else {
        return false;
    };
    proposition_mentions_pointer(relation, pointer) || proposition_mentions_pointer(goal, pointer)
}

fn proposition_mentions_pointer(
    proposition: &Proposition,
    target: &crate::kernel::Address,
) -> bool {
    let mut pending = vec![proposition];
    let mut shared_seen = std::collections::HashSet::new();
    while let Some(current) = pending.pop() {
        match current {
            Proposition::ConditionIs(condition, _) => {
                if let Some(view) =
                    crate::kernel::machine_integer::comparison::structural_comparison_view(
                        condition.old_form(),
                    )
                {
                    for operand in &view.operands {
                        let mut pending = vec![operand.operand_view()];
                        while let Some(term) = pending.pop() {
                            if let crate::kernel::MachineOperandView::Shared(root) = term
                                && !shared_seen.insert(root.id())
                            {
                                continue;
                            }
                            if crate::instrumentation::deadline_exceeded_with_work(1) {
                                return false;
                            }
                            if let Some((_, _, children)) = term.binary() {
                                pending.extend(children);
                            } else if let Some(leaf) = term.read_source()
                                && term_mentions_pointer(&leaf, target)
                            {
                                return true;
                            }
                        }
                    }
                }
            }
            Proposition::And(left, right)
            | Proposition::Or(left, right)
            | Proposition::Implies(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            Proposition::Not(body) => pending.push(body),
            _ => {}
        }
    }
    false
}

fn term_mentions_pointer(term: &OldMachineTerm, target: &crate::kernel::Address) -> bool {
    let mut pending = vec![term];
    while let Some(current) = pending.pop() {
        match current {
            OldMachineTerm::IntegerAddress(pointer, _) => {
                if bounded_address_equal(pointer, target) {
                    return true;
                }
            }
            binary_term!(Bits32, Add, left, right)
            | binary_term!(Bits32, Subtract, left, right)
            | binary_term!(Bits32, Multiply, left, right)
            | OldMachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op:
                    MachineBinaryOp::Add
                    | MachineBinaryOp::Subtract
                    | MachineBinaryOp::Multiply
                    | MachineBinaryOp::Divide
                    | MachineBinaryOp::Remainder
                    | MachineBinaryOp::BitwiseAnd
                    | MachineBinaryOp::BitwiseOr,
                left,
                right,
            }
            | OldMachineTerm::Float32Binary { left, right, .. }
            | OldMachineTerm::Float64Binary { left, right, .. } => {
                pending.push(left);
                pending.push(right);
            }
            OldMachineTerm::PureFunctionApplication { arguments, .. } => {
                pending.extend(arguments.iter());
            }
            _ => {}
        }
    }
    false
}

fn bounded_address_equal(left: &crate::kernel::Address, right: &crate::kernel::Address) -> bool {
    if !bounded_pointer_work(left) || !bounded_pointer_work(right) || left.base != right.base {
        return false;
    }
    let mut pending = vec![(&left.offset, &right.offset)];
    while let Some((left, right)) = pending.pop() {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return false;
        }
        match (left.view(), right.view()) {
            (OffsetView::Constant(a), OffsetView::Constant(b)) => {
                if a != b {
                    return false;
                }
            }
            (OffsetView::Variable(a), OffsetView::Variable(b)) => {
                if a != b {
                    return false;
                }
            }
            (OffsetView::Add(a, b), OffsetView::Add(c, d)) => {
                pending.push((a, c));
                pending.push((b, d));
            }
            (
                OffsetView::Int32Scaled {
                    index: a,
                    byte_width: aw,
                },
                OffsetView::Int32Scaled {
                    index: b,
                    byte_width: bw,
                },
            ) => {
                if aw != bw || !bounded_index_equal(&a, &b) {
                    return false;
                }
            }
            (
                OffsetView::Int64Scaled {
                    index: a,
                    byte_width: aw,
                    ..
                },
                OffsetView::Int64Scaled {
                    index: b,
                    byte_width: bw,
                    ..
                },
            ) => {
                if aw != bw || !bounded_index_equal(&a, &b) {
                    return false;
                }
            }
            _ => return false,
        }
    }
    true
}
fn is_alignment_goal(p: &Proposition) -> bool {
    matches!(p, Proposition::ConditionIs(condition, _) if alignment_shape(condition.old_form()).is_some())
}
fn is_pointer_relation(p: &Proposition) -> bool {
    matches!(&p, condition_source_0 @ Proposition::ConditionIs(
            _,
            true
        ) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::PointerEqual(..)
                | OldConditionTerm::AddressEqual(_, _)
                | OldConditionTerm::AddressOffsetEqual(_, _), _))))
}
fn is_signed_scalar_bound(p: &Proposition) -> bool {
    let Some((
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left: _,
            right: _,
        }
        | OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left: _,
            right: _,
        }
        | OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterThan,
            left: _,
            right: _,
        }
        | OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterEqual,
            left: _,
            right: _,
        },
        true,
    )) = p.old_condition()
    else {
        return false;
    };
    true
}
/// A scalar bound a pointer translation may cite.
fn is_pointer_translation_bound(p: &Proposition) -> bool {
    is_signed_scalar_bound(p) || is_unsigned64_bound(p)
}
/// An unsigned 64-bit order, which bounds a `uint64` index.
fn is_unsigned64_bound(p: &Proposition) -> bool {
    matches!(&p, condition_source_0 @ Proposition::ConditionIs(
            _,
            true,
        ) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessThan,
                left: _,
                right: _
            } | OldConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessEqual,
                left: _,
                right: _
            } | OldConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterThan,
                left: _,
                right: _
            } | OldConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterEqual,
                left: _,
                right: _
            }, _))))
}
fn is_bitvector64_equality(p: &Proposition) -> bool {
    word_comparison_truth(p) == Some(true)
}
fn is_bitvector64_goal(p: &Proposition) -> bool {
    word_comparison_truth(p).is_some()
}
fn word_comparison_truth(p: &Proposition) -> Option<bool> {
    let Proposition::ConditionIs(condition, truth) = p else {
        return None;
    };
    let view = crate::kernel::machine_integer::comparison::structural_comparison_view(
        condition.old_form(),
    )?;
    (matches!(
        view.format,
        MachineIntegerType::Int64 | MachineIntegerType::UInt64
    ) && view.relation == CompareRelation::Equal)
        .then_some(*truth != view.negated)
}
/// Alignment equalities are evidence, not the recorded tagged-word relation.
fn is_word_equality(p: &Proposition) -> bool {
    let Proposition::ConditionIs(condition, _) = p else {
        return false;
    };
    word_comparison_truth(p) == Some(true) && alignment_shape(condition.old_form()).is_none()
}
fn float_finite_premise(goal: &Proposition, premises: &[Proposition]) -> Option<usize> {
    let Proposition::ConditionIs(condition, _) = goal else {
        return None;
    };
    let (width, expression) = match condition.old_form() {
        OldConditionTerm::Float32(FloatCondition::Comparison { left, right, .. })
            if bounded_term_equal(left, right) =>
        {
            (32, left.as_ref())
        }
        OldConditionTerm::Float64(FloatCondition::Comparison { left, right, .. })
            if bounded_term_equal(left, right) =>
        {
            (64, left.as_ref())
        }
        _ => return None,
    };
    premises.iter().position(|p| {
        if !charge_proposition(p) {
            return false;
        }
        match (width, p) {
            (32, condition_source @ Proposition::ConditionIs(_, true))
                if let Some((
                    OldConditionTerm::Float32(FloatCondition::Classification {
                        classification: FloatClassification::Finite,
                        value,
                    }),
                    _,
                )) = condition_source.old_condition() =>
            {
                bounded_term_equal(value, expression)
            }
            (64, condition_source @ Proposition::ConditionIs(_, true))
                if let Some((
                    OldConditionTerm::Float64(FloatCondition::Classification {
                        classification: FloatClassification::Finite,
                        value,
                    }),
                    _,
                )) = condition_source.old_condition() =>
            {
                bounded_term_equal(value, expression)
            }
            _ => false,
        }
    })
}

fn charge_proposition(proposition: &Proposition) -> bool {
    if crate::instrumentation::deadline_exceeded_with_work(1) {
        return false;
    }
    let Proposition::ConditionIs(condition, _) = proposition else {
        return true;
    };
    match condition.old_form() {
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        }
        | OldConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left,
            right,
        }
        | OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left,
            right,
        }
        | OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left,
            right,
        }
        | OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterThan,
            left,
            right,
        }
        | OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterEqual,
            left,
            right,
        } => bounded_term_work(left) && bounded_term_work(right),
        OldConditionTerm::AddressOffsetEqual(left, right) => {
            bounded_offset_work(left) && bounded_offset_work(right)
        }
        OldConditionTerm::AddressEqual(left, right) => {
            bounded_pointer_work(left) && bounded_pointer_work(right)
        }
        OldConditionTerm::Float32(float) | OldConditionTerm::Float64(float) => match float {
            FloatCondition::Comparison { left, right, .. } => {
                bounded_term_work(left) && bounded_term_work(right)
            }
            FloatCondition::Classification { value, .. } => bounded_term_work(value),
        },
        _ => true,
    }
}

fn bounded_offset_work(root: &crate::kernel::AddressOffset) -> bool {
    let mut pending = vec![root];
    let mut count = 0usize;
    while let Some(offset) = pending.pop() {
        count = count.saturating_add(1);
        if count > 256 || crate::instrumentation::deadline_exceeded_with_work(1) {
            return false;
        }
        match offset.view() {
            OffsetView::Add(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            OffsetView::Int32Scaled { index, .. } | OffsetView::Int64Scaled { index, .. }
                if !bounded_index_work(&index) =>
            {
                return false;
            }
            _ => {}
        }
    }
    true
}

fn bounded_term_work(root: &OldMachineTerm) -> bool {
    bounded_term_work_count(root, &mut 0)
}

fn bounded_term_work_count(root: &OldMachineTerm, count: &mut usize) -> bool {
    let mut pending = vec![root];
    while let Some(term) = pending.pop() {
        *count = count.saturating_add(1);
        if *count > 256 || crate::instrumentation::deadline_exceeded_with_work(1) {
            return false;
        }
        match term {
            binary_term!(Bits32, Add, left, right)
            | binary_term!(Bits32, Subtract, left, right)
            | binary_term!(Bits32, Multiply, left, right)
            | OldMachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op:
                    MachineBinaryOp::Add
                    | MachineBinaryOp::Subtract
                    | MachineBinaryOp::Multiply
                    | MachineBinaryOp::Divide
                    | MachineBinaryOp::Remainder
                    | MachineBinaryOp::BitwiseAnd
                    | MachineBinaryOp::BitwiseOr,
                left,
                right,
            } => {
                pending.push(left);
                pending.push(right);
            }
            cast_term!(UInt32From64, value) => pending.push(value),
            OldMachineTerm::MemoryLoad(_, pointer, _) if !bounded_pointer_work(pointer) => {
                return false;
            }
            OldMachineTerm::IntegerAddress(pointer, _) if !bounded_offset_work(&pointer.offset) => {
                return false;
            }
            OldMachineTerm::IntegerAddress(pointer, _)
                if !bounded_address_base_work(&pointer.base) =>
            {
                return false;
            }
            _ => {}
        }
    }
    true
}

fn bounded_pointer_work(pointer: &crate::kernel::Address) -> bool {
    bounded_address_base_work(&pointer.base) && bounded_offset_work(&pointer.offset)
}

fn bounded_address_base_work(block: &crate::kernel::AddressBase) -> bool {
    let size = match block {
        crate::kernel::AddressBase::Concrete(name) | crate::kernel::AddressBase::Function(name) => {
            name.len()
        }
        crate::kernel::AddressBase::StringLiteral { identity, bytes } => {
            identity.payload_bytes().saturating_add(bytes.len())
        }
        _ => 1,
    };
    size <= 256 && !crate::instrumentation::deadline_exceeded_with_work(size.max(1))
}

fn bounded_index_work(root: &crate::kernel::SharedMachineIntegerTerm) -> bool {
    let mut pending = vec![root.operand_view()];
    let mut count = 0usize;
    while let Some(view) = pending.pop() {
        if let Some(leaf) = view
            .literal()
            .map(std::borrow::Cow::Owned)
            .or_else(|| view.read_source())
        {
            if !bounded_term_work_count(&leaf, &mut count) {
                return false;
            }
            continue;
        }
        count += 1;
        if count > 256 || crate::instrumentation::deadline_exceeded_with_work(1) {
            return false;
        }
        if let Some((format, op, operands)) = view.binary() {
            use MachineBinaryOp::*;
            if matches!(
                (format, op),
                (
                    MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    Add | Subtract | Multiply
                ) | (
                    MachineIntegerType::UInt64,
                    Add | Subtract | Multiply | Divide | Remainder | BitwiseAnd | BitwiseOr
                )
            ) {
                pending.extend(operands);
            }
        } else if let Some((crate::kernel::MachineCastSpelling::UInt32From64, _, _, operand)) =
            view.cast()
        {
            pending.push(operand);
        }
    }
    true
}

fn bounded_index_equal(
    left: &crate::kernel::SharedMachineIntegerTerm,
    right: &crate::kernel::SharedMachineIntegerTerm,
) -> bool {
    let mut pending = vec![(left.operand_view(), right.operand_view())];
    let mut count = 0usize;
    while let Some((left, right)) = pending.pop() {
        let a = left
            .literal()
            .map(std::borrow::Cow::Owned)
            .or_else(|| left.read_source());
        let b = right
            .literal()
            .map(std::borrow::Cow::Owned)
            .or_else(|| right.read_source());
        if let (Some(a), Some(b)) = (a, b) {
            if !bounded_term_equal_count(&a, &b, &mut count) {
                return false;
            }
            continue;
        }
        count += 1;
        if count > 256 || crate::instrumentation::deadline_exceeded_with_work(1) {
            return false;
        }
        if let (
            Some((crate::kernel::MachineCastSpelling::UInt32From64, _, _, a)),
            Some((crate::kernel::MachineCastSpelling::UInt32From64, _, _, b)),
        ) = (left.cast(), right.cast())
        {
            pending.push((a, b));
            continue;
        }
        if let (Some((af, ao, [al, ar])), Some((bf, bo, [bl, br]))) =
            (left.binary(), right.binary())
        {
            use MachineBinaryOp::*;
            if (af, ao) != (bf, bo)
                || !matches!(
                    (af, ao),
                    (MachineIntegerType::Int32, Add | Subtract | Multiply)
                        | (
                            MachineIntegerType::UInt64,
                            Add | Subtract | Multiply | BitwiseAnd | BitwiseOr
                        )
                )
            {
                return false;
            }
            pending.push((al, bl));
            pending.push((ar, br));
        } else {
            return false;
        }
    }
    true
}

fn bounded_term_equal(left: &OldMachineTerm, right: &OldMachineTerm) -> bool {
    bounded_term_equal_count(left, right, &mut 0)
}

fn bounded_term_equal_count(
    left: &OldMachineTerm,
    right: &OldMachineTerm,
    count: &mut usize,
) -> bool {
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        *count = count.saturating_add(1);
        if *count > 256 || crate::instrumentation::deadline_exceeded_with_work(1) {
            return false;
        }
        match (left, right) {
            (cast_term!(UInt32From64, left), cast_term!(UInt32From64, right)) => {
                pending.push((left, right))
            }
            (bits32_constant!(a), bits32_constant!(b)) if constant_u32(*a) == constant_u32(*b) => {}
            (int64_constant!(a), int64_constant!(b)) if constant_i64(*a) == constant_i64(*b) => {}
            (uint64_constant!(a), uint64_constant!(b)) if constant_u64(*a) == constant_u64(*b) => {}
            (OldMachineTerm::Variable(a), OldMachineTerm::Variable(b)) if a == b => {}
            (OldMachineTerm::MemoryLoad(lm, lp, lk), OldMachineTerm::MemoryLoad(rm, rp, rk)) => {
                if lm.point() != rm.point() || lk != rk || !bounded_address_equal(lp, rp) {
                    return false;
                }
            }
            (OldMachineTerm::IntegerAddress(_, _), OldMachineTerm::IntegerAddress(_, _)) => {
                return false;
            }
            (
                OldMachineTerm::PureFunctionApplication {
                    name: left_name,
                    arguments: left_arguments,
                },
                OldMachineTerm::PureFunctionApplication {
                    name: right_name,
                    arguments: right_arguments,
                },
            ) if left_name == right_name && left_arguments.len() == right_arguments.len() => {
                pending.extend(left_arguments.iter().zip(right_arguments.iter()));
            }
            _ => {
                use crate::kernel::BitvectorBinaryOp as Op;
                let (Some((operator, a, b)), Some((other, c, d))) =
                    (left.as_binary(), right.as_binary())
                else {
                    return false;
                };
                let compared = matches!(
                    operator,
                    Op::Machine(
                        crate::kernel::MachineIntegerType::Int32,
                        crate::kernel::MachineBinaryOp::Add
                    ) | Op::Machine(
                        crate::kernel::MachineIntegerType::Int32,
                        crate::kernel::MachineBinaryOp::Subtract
                    ) | Op::Machine(
                        crate::kernel::MachineIntegerType::Int32,
                        crate::kernel::MachineBinaryOp::Multiply
                    ) | Op::Machine(
                        MachineIntegerType::UInt64,
                        MachineBinaryOp::Add
                            | MachineBinaryOp::Subtract
                            | MachineBinaryOp::Multiply
                            | MachineBinaryOp::BitwiseAnd
                            | MachineBinaryOp::BitwiseOr
                    ) | Op::Float32(_)
                        | Op::Float64(_)
                );
                if operator != other || !compared {
                    return false;
                }
                pending.push((a, c));
                pending.push((b, d));
            }
        }
    }
    true
}

fn alignment_shape(condition: &OldConditionTerm) -> Option<(&crate::kernel::Address, u64)> {
    crate::kernel::proof::arithmetic_special::checked_pointer_alignment(condition)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{ComparisonOperator as KernelComparisonOperator, OldMachineTerm, Variable};

    fn bound(value: usize) -> SyntaxProposition {
        SyntaxProposition::Comparison {
            left: SyntaxTerm::IntegerLiteral("0".to_string()),
            operator: ComparisonOperator::LessEqual,
            right: SyntaxTerm::IntegerLiteral(value.to_string()),
        }
    }

    #[test]
    fn certificates_keep_only_the_premises_their_nodes_cite() {
        let premises = (0..6).map(bound).collect::<Vec<_>>();
        let goal = bound(99);
        let nodes = vec![
            SpecialArithmeticNode::PointerTranslation {
                relation: 4,
                bounds: vec![1, 4],
                result: goal.clone(),
            },
            SpecialArithmeticNode::SignedDefined {
                width: crate::kernel::SignedDefinedWidth::Int32,
                bounds: vec![1],
                result: goal.clone(),
            },
            SpecialArithmeticNode::PointerAlignment {
                premise: None,
                result: goal.clone(),
            },
        ];
        let (kept, nodes) = cited_premises_only(&premises, nodes);
        assert_eq!(kept, vec![bound(1), bound(4)]);
        assert_eq!(
            nodes,
            vec![
                SpecialArithmeticNode::PointerTranslation {
                    relation: 1,
                    bounds: vec![0, 1],
                    result: goal.clone(),
                },
                SpecialArithmeticNode::SignedDefined {
                    width: crate::kernel::SignedDefinedWidth::Int32,
                    bounds: vec![0],
                    result: goal.clone(),
                },
                SpecialArithmeticNode::PointerAlignment {
                    premise: None,
                    result: goal,
                },
            ]
        );
    }

    #[test]
    fn deep_float_candidate_is_rejected_before_recursive_helpers() {
        let mut term = OldMachineTerm::Variable(Variable(1));
        for _ in 0..300 {
            term = binary_node!(
                Int32,
                Add,
                Box::new(term),
                Box::new(OldMachineTerm::constant(1))
            );
        }
        let goal = Proposition::condition_is(
            OldConditionTerm::Float32(FloatCondition::Comparison {
                operator: KernelComparisonOperator::Equal,
                left: Box::new(term.clone()),
                right: Box::new(term.clone()),
            }),
            true,
        );
        let finite = Proposition::condition_is(
            OldConditionTerm::Float32(FloatCondition::Classification {
                classification: FloatClassification::Finite,
                value: Box::new(term),
            }),
            true,
        );
        assert!(plan_special_arithmetic(&goal, &[finite]).is_none());
    }

    #[test]
    fn finite_candidate_scan_charges_unrelated_premises() {
        let value = OldMachineTerm::Variable(Variable(2));
        let goal = Proposition::condition_is(
            OldConditionTerm::Float32(FloatCondition::Comparison {
                operator: KernelComparisonOperator::Equal,
                left: Box::new(value.clone()),
                right: Box::new(value.clone()),
            }),
            true,
        );
        let mut premises = (0..64)
            .map(|i| {
                Proposition::condition_is(
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(OldMachineTerm::Variable(Variable(100 + i))),
                        right: Box::new(OldMachineTerm::constant(i as u32)),
                    },
                    true,
                )
            })
            .collect::<Vec<_>>();
        premises.push(Proposition::condition_is(
            OldConditionTerm::Float32(FloatCondition::Classification {
                classification: FloatClassification::Finite,
                value: Box::new(value),
            }),
            true,
        ));
        let plan = plan_special_arithmetic(&goal, &premises).expect("finite plan");
        assert!(matches!(
            plan.nodes[0],
            KernelNode::FloatReflexive { finite: 64, .. }
        ));
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/surface/checking/special_arithmetic_planner/tests.rs");
}
