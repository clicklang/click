//! One explicit equality transports one whole operand of an Integer relation.
//! No nonlinear search, recursive substitution, or ambient fact lookup.
use super::arithmetic_special::ArithmeticRuleError as Error;
use crate::kernel::{ConditionTerm, Proposition, SharedIntegerTerm};
fn relation(proposition: &Proposition) -> Option<(&SharedIntegerTerm, &SharedIntegerTerm, bool)> {
    match proposition {
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((ConditionTerm::IntegerLessEqual(a, b), _)) =
                condition_source_0.condition_native() =>
        {
            Some((a, b, false))
        }
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((ConditionTerm::IntegerEqual(a, b), _)) =
                condition_source_0.condition_native() =>
        {
            Some((a, b, true))
        }
        _ => None,
    }
}

/// Transport one entire operand of an equality or non-strict bound.
/// Operand identities are shared DAG nodes; no subexpression or ambient search.
pub(super) fn check(
    node: usize,
    bounds: &[usize],
    premises: &[Proposition],
    result: &Proposition,
) -> Result<(), Error> {
    let invalid = || Error::InvalidIntegerRelationTransport(node);
    if crate::instrumentation::deadline_exceeded_with_work(5) {
        return Err(Error::WorkLimitExceeded);
    }
    if bounds.len() != 2 {
        return Err(invalid());
    }
    let Some((ConditionTerm::IntegerEqual(a, b), true)) = (premises
        .get(bounds[0])
        .ok_or(Error::InvalidPremise(bounds[0]))?)
    .condition_native() else {
        return Err(invalid());
    };
    let (lo, hi, equality) = relation(
        premises
            .get(bounds[1])
            .ok_or(Error::InvalidPremise(bounds[1]))?,
    )
    .ok_or_else(invalid)?;
    let (new_lo, new_hi, new_equality) = relation(result).ok_or_else(invalid)?;
    if equality != new_equality {
        return Err(invalid());
    }
    let equal =
        |x: &SharedIntegerTerm, y: &SharedIntegerTerm| (x == a && y == b) || (x == b && y == a);
    if (new_lo == lo && equal(hi, new_hi)) || (new_hi == hi && equal(lo, new_lo)) {
        Ok(())
    } else {
        Err(invalid())
    }
}
