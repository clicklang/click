//! The one entry point to Click's arithmetic proof planners.
//!
//! Each planner reads only the goal and the premise slice its caller passes,
//! and Surface expands its plan into ordinary checked proof steps. Every caller outside
//! this module plans through [`plan_arithmetic`], [`arithmetic_plans`], or
//! [`refute_integer_goal`], so the engines `arithmetic` owns, and the order
//! it tries them in, are written once (`roadmap/smart-tactics.md`, plan steps
//! 5 and 6).

use super::integer_affine_planner::plan_integer_affine;
use super::integer_refutation_planner::{IntegerRefutation, plan_integer_refutation_with_ranges};
use super::signed_arithmetic_planner::{
    plan_signed_arithmetic, plan_signed_arithmetic_with_weakening,
};
use super::special_arithmetic_planner::plan_special_arithmetic;
use crate::kernel::proof::arithmetic_special::SpecialArithmeticPlan;
use crate::kernel::proof::integer_arithmetic::{IntegerArithmeticNode, IntegerArithmeticPlan};
use crate::kernel::proof::signed_arithmetic::SignedArithmeticPlan;
use crate::kernel::{ConditionTerm, IntegerTerm, MachineBinaryOp, Proposition};

/// One arithmetic proof planner.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::surface) enum ArithmeticEngine {
    /// Pointer, finite-float, and signed-constant facts.
    Special,
    /// The mathematical `Integer` affine fragment.
    IntegerAffine,
    /// Signed `int32` comparisons and equalities.
    SignedInt32,
    /// [`Self::SignedInt32`], also allowed the checked weakening step an
    /// explicit `arithmetic() using` may request.
    SignedInt32WithWeakening,
    /// An `Integer` bound refuted by simplex: any number of premises, with
    /// no case splits.
    IntegerRefutation,
}

/// A planned certificate, tagged by the engine that planned it.
#[derive(Clone, Debug)]
pub(in crate::surface) enum ArithmeticPlan {
    Special(SpecialArithmeticPlan),
    IntegerAffine(IntegerArithmeticPlan),
    SignedInt32(SignedArithmeticPlan),
}

impl ArithmeticPlan {
    pub(in crate::surface) fn special(self) -> Option<SpecialArithmeticPlan> {
        match self {
            Self::Special(plan) => Some(plan),
            _ => None,
        }
    }

    pub(in crate::surface) fn integer_affine(self) -> Option<IntegerArithmeticPlan> {
        match self {
            Self::IntegerAffine(plan) => Some(plan),
            _ => None,
        }
    }

    pub(in crate::surface) fn signed_int32(self) -> Option<SignedArithmeticPlan> {
        match self {
            Self::SignedInt32(plan) => Some(plan),
            _ => None,
        }
    }
}

/// Plans `goal` from exactly `premises` with one engine.
pub(in crate::surface) fn plan_arithmetic(
    engine: ArithmeticEngine,
    goal: &Proposition,
    premises: &[Proposition],
) -> Option<ArithmeticPlan> {
    match engine {
        ArithmeticEngine::Special => {
            plan_special_arithmetic(goal, premises).map(ArithmeticPlan::Special)
        }
        ArithmeticEngine::IntegerAffine => {
            plan_integer_affine(goal, premises).map(ArithmeticPlan::IntegerAffine)
        }
        ArithmeticEngine::SignedInt32 => {
            plan_signed_arithmetic(goal, premises).map(ArithmeticPlan::SignedInt32)
        }
        ArithmeticEngine::SignedInt32WithWeakening => {
            plan_signed_arithmetic_with_weakening(goal, premises).map(ArithmeticPlan::SignedInt32)
        }
        ArithmeticEngine::IntegerRefutation => {
            let plan =
                |ranges: &[crate::kernel::IntegerTerm]| match plan_integer_refutation_with_ranges(
                    goal, premises, ranges,
                ) {
                    IntegerRefutation::Proved {
                        certificate,
                        premises: used,
                    } => cited_by_caller_index(certificate, &used, premises)
                        .map(ArithmeticPlan::IntegerAffine),
                    _ => None,
                };
            // A refutation that misses from the listed premises alone is
            // planned once more with the type range of each machine value
            // they and the goal observe, as `solve`'s refutation is: that
            // `k < x` and `x == 0u64` leave no unsigned `k` is the range,
            // not a premise. A range enters the certificate as a checked
            // `TypeRange` node, not as a fact.
            plan(&[]).or_else(|| {
                let ranges = machine_observations(goal, premises);
                (!ranges.is_empty()).then(|| plan(&ranges)).flatten()
            })
        }
    }
}

/// Each observed machine value, including the input of a fixed unsigned
/// right shift whose operation bound may need the input's type range.
pub(in crate::surface) fn machine_observations(
    goal: &Proposition,
    premises: &[Proposition],
) -> Vec<crate::kernel::IntegerTerm> {
    let mut seen = std::collections::HashSet::new();
    let values = std::iter::once(goal)
        .chain(premises)
        .flat_map(crate::kernel::proof::integer_arithmetic::integer_affine_machine_values)
        .collect::<Vec<_>>();
    let operands = values.iter().filter_map(|value| {
        if value.ty().format().is_signed()
            || !matches!(
                value.operand_view().binary(),
                Some((_, MachineBinaryOp::ShiftRight, _))
            )
        {
            return None;
        }
        let bound = crate::kernel::machine_integer::bounds::operation_bound(value, false)?;
        let (ConditionTerm::IntegerLessEqual(_, input), true) = bound.condition_native()? else {
            return None;
        };
        let IntegerTerm::Machine(input) = input.as_ref() else {
            return None;
        };
        Some(input.clone())
    });
    values
        .iter()
        .cloned()
        .chain(operands)
        .filter(|value| seen.insert(value.id()))
        .map(IntegerTerm::Machine)
        .collect()
}

/// Renumbers a refutation's premise nodes, which index the premises it
/// used, to index `premises`, the caller's list.
fn cited_by_caller_index(
    mut certificate: IntegerArithmeticPlan,
    used: &[Proposition],
    premises: &[Proposition],
) -> Option<IntegerArithmeticPlan> {
    let positions = used
        .iter()
        .map(|premise| premises.iter().position(|candidate| candidate == premise))
        .collect::<Option<Vec<_>>>()?;
    for node in &mut certificate.nodes {
        if let IntegerArithmeticNode::Premise { index, .. }
        | IntegerArithmeticNode::ExcludedTypeBound { index, .. }
        | IntegerArithmeticNode::StrictFromDisequal {
            disequal: index, ..
        } = node
        {
            *index = *positions.get(*index)?;
        }
    }
    Some(certificate)
}

/// The plans of `arithmetic`'s engines for `goal` from exactly `premises`, in
/// the order it tries them: special, then `Integer` affine, then signed
/// `int32` (with the weakening step when `weakening` is set), then simplex
/// refutation, which proves what the bounded affine planner's premise
/// combinations miss. Each engine
/// plans only when the caller asks for the next plan, so a caller that takes
/// the first plan it can apply runs no later planner.
pub(in crate::surface) fn arithmetic_plans<'a>(
    goal: &'a Proposition,
    premises: &'a [Proposition],
    weakening: bool,
) -> impl Iterator<Item = ArithmeticPlan> + 'a {
    let signed = if weakening {
        ArithmeticEngine::SignedInt32WithWeakening
    } else {
        ArithmeticEngine::SignedInt32
    };
    [
        ArithmeticEngine::Special,
        ArithmeticEngine::IntegerAffine,
        signed,
        ArithmeticEngine::IntegerRefutation,
    ]
    .into_iter()
    .filter_map(move |engine| plan_arithmetic(engine, goal, premises))
}

/// Refutes the `Integer` negation of `goal` from exactly `premises` by
/// simplex, also using the type range of each machine observation in
/// `ranges`. This is selected-premise arithmetic, which also selects the
/// premises and the ranges; [`ArithmeticEngine::IntegerRefutation`] is the same planner
/// over exactly the caller's premises.
pub(in crate::surface) fn refute_integer_goal(
    goal: &Proposition,
    premises: &[Proposition],
    ranges: &[IntegerTerm],
) -> IntegerRefutation {
    plan_integer_refutation_with_ranges(goal, premises, ranges)
}
