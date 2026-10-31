//! Trusted separation rules. Constructors retain exactly the written premises;
//! they do not search the fact store or inspect memory history.
use super::prelude::*;

/// Distinct indices of one typed array describe disjoint complete elements.
/// Pointer offsets use exact scaled coordinates, not modular byte arithmetic.
pub(crate) fn prove_separation_elements(
    base: CPointerValue,
    width: u32,
    i: Bitvector32Term,
    j: Bitvector32Term,
) -> Theorem {
    assert!(width > 0, "elements require a nonzero storage width");
    crate::instrumentation::record_deterministic_work(1);
    let element = |index: Bitvector32Term| {
        let address = base
            .pointer()
            .offset_by_typed_elements(index, width, true, true);
        CResource::Memory(CMemoryRange::from_pointer_value(
            &base.clone().with_address(address),
            0u32.into(),
            1u32.into(),
            width,
        ))
    };
    Theorem::new(Proposition::Implies(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::int64_equal(i.clone(), j.clone()),
            false,
        )),
        Box::new(Proposition::CResourceSeparate {
            left: Box::new(element(i)),
            right: Box::new(element(j)),
        }),
    ))
}

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
