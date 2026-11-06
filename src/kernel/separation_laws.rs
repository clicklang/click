//! Trusted separation rules. Constructors retain exactly the written premises;
//! they do not search the fact store or inspect memory history.
use super::prelude::*;

/// Distinct indices of one typed array describe disjoint complete elements.
/// Pointer offsets use exact scaled coordinates, not modular byte arithmetic.
pub(crate) fn prove_separation_elements(
    base: CPointerValue,
    width: u32,
    format: MachineIntegerType,
    i: MachineTerm,
    j: MachineTerm,
) -> Theorem {
    assert!(width > 0, "elements require a nonzero storage width");
    let (unsigned, wide) = match format {
        MachineIntegerType::Int32 => (false, false),
        MachineIntegerType::Int64 => (false, true),
        MachineIntegerType::UInt64 => (true, true),
        _ => panic!("elements indices require int32, int64, or uint64"),
    };
    crate::instrumentation::record_deterministic_work(1);
    let element = |index: MachineTerm| {
        let address = base
            .pointer()
            .offset_by_typed_elements(index, width, unsigned, wide);
        CResource::Memory(CMemoryRange::from_pointer_value(
            &base.clone().with_address(address),
            0u32.into(),
            1u32.into(),
            width,
        ))
    };
    Theorem::new(Proposition::Implies(
        Box::new(Proposition::ConditionIs(
            if wide {
                ConditionTerm::int64_equal(i.clone(), j.clone())
            } else {
                ConditionTerm::equal(i.clone(), j.clone())
            },
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
    lo: MachineTerm,
    hi: MachineTerm,
    inner_lo: MachineTerm,
    inner_hi: MachineTerm,
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

/// Resource laws construct only the explicitly supplied proposition tree.
/// They neither inspect ownership nor discover containment paths.
pub(crate) fn prove_resource_law(name: &str, args: &[CResource]) -> Option<Theorem> {
    let contains = |a: &CResource, b: &CResource| Proposition::CResourceContains {
        parent: Box::new(a.clone()),
        child: Box::new(b.clone()),
    };
    let separate = |a: &CResource, b: &CResource| Proposition::CResourceSeparate {
        left: Box::new(a.clone()),
        right: Box::new(b.clone()),
    };
    crate::instrumentation::record_deterministic_work(1);
    let (premises, conclusion) = match (name, args) {
        ("click::separation::contains_refl", [a]) => (vec![], contains(a, a)),
        ("click::separation::contains_trans", [a, b, c]) => {
            (vec![contains(a, b), contains(b, c)], contains(a, c))
        }
        ("click::separation::contains_left", [a, b]) => {
            (vec![], contains(&CResource::star(a.clone(), b.clone()), a))
        }
        ("click::separation::contains_right", [a, b]) => {
            (vec![], contains(&CResource::star(a.clone(), b.clone()), b))
        }
        ("click::separation::separate_symm", [a, b]) => (vec![separate(a, b)], separate(b, a)),
        ("click::separation::separate_star", [a, b, c]) => (
            vec![separate(a, c), separate(b, c)],
            separate(&CResource::star(a.clone(), b.clone()), c),
        ),
        ("click::separation::separate_emp", [a]) => (vec![], separate(&CResource::Emp, a)),
        _ => return None,
    };
    Some(Theorem::new(
        premises
            .into_iter()
            .rev()
            .fold(conclusion, |body, premise| {
                Proposition::Implies(Box::new(premise), Box::new(body))
            }),
    ))
}

/// Viewability is a pure state-indexed fact, not resource ownership. Memory
/// descriptors use the existing atom so both Surface spellings coincide.
pub(crate) fn resource_viewable(memory: &CMemory, resource: CResource) -> Proposition {
    match resource {
        CResource::Memory(range) => range.loadable_fact(memory),
        resource => Proposition::CResourceViewable {
            memory: memory.clone(),
            resource: Box::new(resource),
        },
    }
}

pub(crate) fn prove_viewable_restrict(
    memory: &CMemory,
    parent: CResource,
    child: CResource,
) -> Theorem {
    crate::instrumentation::record_deterministic_work(1);
    Theorem::new(Proposition::Implies(
        Box::new(resource_viewable(memory, parent.clone())),
        Box::new(Proposition::Implies(
            Box::new(Proposition::CResourceContains {
                parent: Box::new(parent),
                child: Box::new(child.clone()),
            }),
            Box::new(resource_viewable(memory, child)),
        )),
    ))
}
