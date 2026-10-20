//! The one entry point to Click's arithmetic certificate planners.
//!
//! Each planner reads only the goal and the premise slice its caller passes,
//! and the kernel checks whatever certificate it returns. Every caller outside
//! this module plans through [`plan_arithmetic`], [`arithmetic_plans`], or
//! [`refute_integer_goal`], so the engines `arithmetic` owns, and the order
//! it tries them in, are written once (`issues/smart-tactics.md`, plan steps
//! 5 and 6).

use super::integer_affine_planner::plan_integer_affine_certificate;
use super::integer_refutation_planner::{IntegerRefutation, plan_integer_refutation_with_ranges};
use super::signed_arithmetic_planner::{
    plan_signed_arithmetic_certificate, plan_signed_arithmetic_certificate_with_weakening,
};
use super::special_arithmetic_planner::plan_special_arithmetic_certificate;
use crate::kernel::proof::arithmetic_special::SpecialArithmeticCertificate;
use crate::kernel::proof::integer_arithmetic::IntegerArithmeticCertificate;
use crate::kernel::proof::signed_arithmetic::SignedArithmeticCertificate;
use crate::kernel::{IntegerTerm, Proposition};

/// One arithmetic certificate planner.
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
}

/// A planned certificate, tagged by the engine that planned it.
#[derive(Clone, Debug)]
pub(in crate::surface) enum ArithmeticPlan {
    Special(SpecialArithmeticCertificate),
    IntegerAffine(IntegerArithmeticCertificate),
    SignedInt32(SignedArithmeticCertificate),
}

impl ArithmeticPlan {
    pub(in crate::surface) fn special(self) -> Option<SpecialArithmeticCertificate> {
        match self {
            Self::Special(plan) => Some(plan),
            _ => None,
        }
    }

    pub(in crate::surface) fn integer_affine(self) -> Option<IntegerArithmeticCertificate> {
        match self {
            Self::IntegerAffine(plan) => Some(plan),
            _ => None,
        }
    }

    pub(in crate::surface) fn signed_int32(self) -> Option<SignedArithmeticCertificate> {
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
            plan_special_arithmetic_certificate(goal, premises).map(ArithmeticPlan::Special)
        }
        ArithmeticEngine::IntegerAffine => {
            plan_integer_affine_certificate(goal, premises).map(ArithmeticPlan::IntegerAffine)
        }
        ArithmeticEngine::SignedInt32 => {
            plan_signed_arithmetic_certificate(goal, premises).map(ArithmeticPlan::SignedInt32)
        }
        ArithmeticEngine::SignedInt32WithWeakening => {
            plan_signed_arithmetic_certificate_with_weakening(goal, premises)
                .map(ArithmeticPlan::SignedInt32)
        }
    }
}

/// The plans of `arithmetic`'s engines for `goal` from exactly `premises`, in
/// the order it tries them: special, then `Integer` affine, then signed
/// `int32` (with the weakening step when `weakening` is set). Each engine
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
    ]
    .into_iter()
    .filter_map(move |engine| plan_arithmetic(engine, goal, premises))
}

/// Refutes the `Integer` negation of `goal` from exactly `premises` by
/// simplex, also using the type range of each machine observation in
/// `ranges`. This is `auto`'s solver; `arithmetic_plans` does not try it yet
/// (`issues/smart-tactics.md`, plan step 6).
pub(in crate::surface) fn refute_integer_goal(
    goal: &Proposition,
    premises: &[Proposition],
    ranges: &[IntegerTerm],
) -> IntegerRefutation {
    plan_integer_refutation_with_ranges(goal, premises, ranges)
}
