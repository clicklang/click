//! Trusted separation rules. Constructors retain exactly the written premises;
//! they do not search the fact store or inspect memory history.
use super::prelude::*;

pub(crate) fn prove_separation_restrict(
    left: CResource,
    right: CResource,
    left_part: CResource,
    right_part: CResource,
) -> Theorem {
    let premises = [
        Proposition::CResourceSeparate {
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        },
        Proposition::CResourceContains {
            parent: Box::new(left),
            child: Box::new(left_part.clone()),
        },
        Proposition::CResourceContains {
            parent: Box::new(right),
            child: Box::new(right_part.clone()),
        },
    ];
    Theorem::new(premises.into_iter().rev().fold(
        Proposition::CResourceSeparate {
            left: Box::new(left_part),
            right: Box::new(right_part),
        },
        |body, premise| Proposition::Implies(Box::new(premise), Box::new(body)),
    ))
}

/// A nested element interval denotes a contained resource. Both ranges are
/// constructed with one base and width; no facts or memory are inspected.
pub(crate) fn prove_separation_subrange(
    base: CPointerValue,
    width: u32,
    lo: Bitvector32Term,
    hi: Bitvector32Term,
    inner_lo: Bitvector32Term,
    inner_hi: Bitvector32Term,
) -> Theorem {
    crate::instrumentation::record_deterministic_work(1);
    let premises = [
        (lo.clone(), inner_lo.clone()),
        (inner_lo.clone(), inner_hi.clone()),
        (inner_hi.clone(), hi.clone()),
    ];
    let conclusion = Proposition::CResourceContains {
        parent: Box::new(CResource::Memory(CMemoryRange::from_pointer_value(
            &base, lo, hi, width,
        ))),
        child: Box::new(CResource::Memory(CMemoryRange::from_pointer_value(
            &base, inner_lo, inner_hi, width,
        ))),
    };
    Theorem::new(
        premises
            .into_iter()
            .rev()
            .fold(conclusion, |body, (left, right)| {
                Proposition::Implies(
                    Box::new(Proposition::ConditionIs(
                        ConditionTerm::signed_less_equal(left, right),
                        true,
                    )),
                    Box::new(body),
                )
            }),
    )
}

#[cfg(test)]
mod scaling_tests {
    include!("../scaling_tests/kernel/separation_laws.rs");
}
