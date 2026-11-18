//! Exclude one constant from one explicit non-strict Integer bound.
use super::arithmetic_special::ArithmeticRuleError as Error;
use crate::kernel::{ConditionTerm, Proposition};

pub(super) fn check(
    node: usize,
    bounds: &[usize],
    premises: &[Proposition],
    result: &Proposition,
) -> Result<(), Error> {
    let invalid = || Error::InvalidIntegerBoundExclusion(node);
    if crate::instrumentation::deadline_exceeded_with_work(5) {
        return Err(Error::WorkLimitExceeded);
    }
    if bounds.len() != 1 {
        return Err(invalid());
    }
    let (a, b) = match result {
        condition_source @ Proposition::ConditionIs(_, _)
            if let Some(
                (ConditionTerm::IntegerNotEqual(a, b), true)
                | (ConditionTerm::IntegerEqual(a, b), false),
            ) = condition_source.condition_native() =>
        {
            (a, b)
        }
        _ => return Err(invalid()),
    };
    let (term, excluded) = if let Some(c) = a.as_const() {
        (b, c)
    } else if let Some(c) = b.as_const() {
        (a, c)
    } else {
        return Err(invalid());
    };
    let Some((ConditionTerm::IntegerLessEqual(lo, hi), true)) = (premises
        .get(bounds[0])
        .ok_or(Error::InvalidPremise(bounds[0]))?)
    .condition_native() else {
        return Err(invalid());
    };
    let (endpoint, lower) = if hi == term {
        (lo.as_const(), true)
    } else if lo == term {
        (hi.as_const(), false)
    } else {
        return Err(invalid());
    };
    let endpoint = endpoint.ok_or_else(invalid)?;
    let work = usize::try_from(endpoint.bits())
        .unwrap_or(usize::MAX)
        .saturating_add(usize::try_from(excluded.bits()).unwrap_or(usize::MAX))
        .saturating_add(16);
    if crate::instrumentation::deadline_exceeded_with_work(work) {
        return Err(Error::WorkLimitExceeded);
    }
    if if lower {
        excluded < endpoint
    } else {
        excluded > endpoint
    } {
        Ok(())
    } else {
        Err(invalid())
    }
}
