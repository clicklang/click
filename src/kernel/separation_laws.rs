//! Trusted separation rules. Constructors retain exactly the written premises;
//! they do not search the fact store or inspect memory history.
use super::prelude::*;

/// Distinct indices of one typed array describe disjoint complete elements.
/// Pointer offsets use exact scaled coordinates, not modular byte arithmetic.
pub(crate) fn prove_separation_elements(
    base: PointerValue,
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
        Resource::Memory(MemoryRange::from_pointer_value(
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
        Box::new(Proposition::ResourceSeparate {
            left: Box::new(element(i)),
            right: Box::new(element(j)),
        }),
    ))
}

/// Distinct indices of one typed array give distinct element addresses:
/// `i != j` implies `&p[i] != &p[j]`. Like [`prove_separation_elements`], the
/// addresses are the exact scaled offsets `p + i * width` and `p + j * width`,
/// which are equal exactly when the indices are (memory resolution reads
/// scaled offsets the same way), and the premise is the index disequality in
/// the index format.
pub(crate) fn prove_separation_distinct_elements(
    base: PointerValue,
    width: u32,
    format: MachineIntegerType,
    i: MachineTerm,
    j: MachineTerm,
) -> Theorem {
    assert!(
        width > 0,
        "element addresses require a nonzero storage width"
    );
    let (unsigned, wide) = match format {
        MachineIntegerType::Int32 => (false, false),
        MachineIntegerType::Int64 => (false, true),
        MachineIntegerType::UInt64 => (true, true),
        _ => panic!("element addresses require int32, int64, or uint64 indices"),
    };
    crate::instrumentation::record_deterministic_work(1);
    let address = |index: MachineTerm| {
        base.pointer()
            .offset_by_typed_elements(index, width, unsigned, wide)
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
        Box::new(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(address(i), address(j)),
            false,
        )),
    ))
}

pub(crate) fn prove_separation_restrict(
    left: Resource,
    right: Resource,
    left_part: Resource,
    right_part: Resource,
) -> Theorem {
    let premises = [
        Proposition::ResourceSeparate {
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        },
        Proposition::ResourceContains {
            parent: Box::new(left),
            child: Box::new(left_part.clone()),
        },
        Proposition::ResourceContains {
            parent: Box::new(right),
            child: Box::new(right_part.clone()),
        },
    ];
    Theorem::new(premises.into_iter().rev().fold(
        Proposition::ResourceSeparate {
            left: Box::new(left_part),
            right: Box::new(right_part),
        },
        |body, premise| Proposition::Implies(Box::new(premise), Box::new(body)),
    ))
}

/// A nested element interval denotes a contained resource. Both ranges are
/// constructed with one base and width; no facts or memory are inspected.
pub(crate) fn prove_separation_subrange(
    base: PointerValue,
    width: u32,
    format: MachineIntegerType,
    lo: MachineTerm,
    hi: MachineTerm,
    inner_lo: MachineTerm,
    inner_hi: MachineTerm,
) -> Theorem {
    assert!(matches!(
        format,
        MachineIntegerType::Int32 | MachineIntegerType::UInt64
    ));
    crate::instrumentation::record_deterministic_work(1);
    let premises = [
        (lo.clone(), inner_lo.clone()),
        (inner_lo.clone(), inner_hi.clone()),
        (inner_hi.clone(), hi.clone()),
    ];
    let range = |start, end| match format {
        MachineIntegerType::Int32 => MemoryRange::from_pointer_value(&base, start, end, width),
        MachineIntegerType::UInt64 => {
            MemoryRange::from_pointer_value_wide(&base, start, end, width)
        }
        _ => unreachable!(),
    };
    let conclusion = Proposition::ResourceContains {
        parent: Box::new(Resource::Memory(range(lo, hi))),
        child: Box::new(Resource::Memory(range(inner_lo, inner_hi))),
    };
    Theorem::new(
        premises
            .into_iter()
            .rev()
            .fold(conclusion, |body, (left, right)| {
                Proposition::Implies(
                    Box::new(Proposition::ConditionIs(
                        ConditionTerm::machine_compare(
                            format,
                            CompareRelation::LessEqual,
                            left,
                            right,
                        ),
                        true,
                    )),
                    Box::new(body),
                )
            }),
    )
}

/// Rebase the same interval to its first element. The explicit nonnegative
/// ordered bounds make the subtraction exact in both admitted formats.
/// This constructs descriptors; it neither grants ownership nor reads facts.
pub(crate) fn prove_separation_rebase(
    base: PointerValue,
    width: u32,
    format: MachineIntegerType,
    lo: MachineTerm,
    hi: MachineTerm,
) -> Theorem {
    assert!(width > 0);
    assert!(matches!(
        format,
        MachineIntegerType::Int32 | MachineIntegerType::UInt64
    ));
    crate::instrumentation::record_deterministic_work(1);
    let wide = format == MachineIntegerType::UInt64;
    let zero = if wide {
        MachineTerm::uint64_constant(0)
    } else {
        MachineTerm::constant(0)
    };
    let length = if wide {
        MachineTerm::uint64_subtract(hi.clone(), lo.clone())
    } else {
        MachineTerm::subtract(hi.clone(), lo.clone())
    };
    let shifted = base
        .clone()
        .with_address(
            base.pointer()
                .offset_by_typed_elements(lo.clone(), width, wide, wide),
        );
    let range = |pointer: &PointerValue, start, end| {
        if wide {
            MemoryRange::from_pointer_value_wide(pointer, start, end, width)
        } else {
            MemoryRange::from_pointer_value(pointer, start, end, width)
        }
    };
    let conclusion = Proposition::ResourceContains {
        parent: Box::new(Resource::Memory(range(&base, lo.clone(), hi.clone()))),
        child: Box::new(Resource::Memory(range(&shifted, zero.clone(), length))),
    };
    // Retain the declaration's exact observation premise even for unsigned
    // indices, where a native zero comparison would simplify to `true`.
    let nonnegative = ConditionTerm::IntegerLessEqual(
        IntegerTerm::constant_i64(0).into(),
        IntegerTerm::from_machine(format, lo.clone())
            .expect("rebase admits machine integer bounds")
            .into(),
    );
    let ordered = ConditionTerm::machine_compare(format, CompareRelation::LessEqual, lo, hi);
    Theorem::new([nonnegative, ordered].into_iter().rev().fold(
        conclusion,
        |body, condition| {
            Proposition::Implies(
                Box::new(Proposition::ConditionIs(condition, true)),
                Box::new(body),
            )
        },
    ))
}

/// An explicitly bounded index denotes one complete element of its interval.
/// Offset construction is exact; no wrapping `i + 1` endpoint is introduced.
pub(crate) fn prove_separation_contains_element(
    base: PointerValue,
    width: u32,
    format: MachineIntegerType,
    lo: MachineTerm,
    hi: MachineTerm,
    index: MachineTerm,
) -> Theorem {
    assert!(width > 0);
    assert!(matches!(
        format,
        MachineIntegerType::Int32 | MachineIntegerType::UInt64
    ));
    crate::instrumentation::record_deterministic_work(1);
    let wide = format == MachineIntegerType::UInt64;
    let parent = if wide {
        MemoryRange::from_pointer_value_wide(&base, lo.clone(), hi.clone(), width)
    } else {
        MemoryRange::from_pointer_value(&base, lo.clone(), hi.clone(), width)
    };
    let address = base
        .pointer()
        .offset_by_typed_elements(index.clone(), width, wide, wide);
    let child = MemoryRange::from_pointer_value(
        &base.with_address(address),
        0u32.into(),
        1u32.into(),
        width,
    );
    let conclusion = Proposition::ResourceContains {
        parent: Box::new(Resource::Memory(parent)),
        child: Box::new(Resource::Memory(child)),
    };
    Theorem::new(
        [
            (CompareRelation::LessEqual, lo, index.clone()),
            (CompareRelation::LessThan, index, hi),
        ]
        .into_iter()
        .rev()
        .fold(conclusion, |body, (relation, left, right)| {
            Proposition::Implies(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::machine_compare(format, relation, left, right),
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
pub(crate) fn prove_resource_law(name: &str, args: &[Resource]) -> Option<Theorem> {
    let contains = |a: &Resource, b: &Resource| Proposition::ResourceContains {
        parent: Box::new(a.clone()),
        child: Box::new(b.clone()),
    };
    let separate = |a: &Resource, b: &Resource| Proposition::ResourceSeparate {
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
            (vec![], contains(&Resource::star(a.clone(), b.clone()), a))
        }
        ("click::separation::contains_right", [a, b]) => {
            (vec![], contains(&Resource::star(a.clone(), b.clone()), b))
        }
        ("click::separation::separate_symm", [a, b]) => (vec![separate(a, b)], separate(b, a)),
        ("click::separation::separate_star", [a, b, c]) => (
            vec![separate(a, c), separate(b, c)],
            separate(&Resource::star(a.clone(), b.clone()), c),
        ),
        ("click::separation::separate_emp", [a]) => (vec![], separate(&Resource::Emp, a)),
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
pub(crate) fn resource_viewable(memory: &Memory, resource: Resource) -> Proposition {
    match resource {
        Resource::Memory(range) => range.loadable_fact(memory),
        resource => Proposition::ResourceViewable {
            memory: memory.clone(),
            resource: Box::new(resource),
        },
    }
}

pub(crate) fn prove_viewable_restrict(
    memory: &Memory,
    parent: Resource,
    child: Resource,
) -> Theorem {
    crate::instrumentation::record_deterministic_work(1);
    Theorem::new(Proposition::Implies(
        Box::new(resource_viewable(memory, parent.clone())),
        Box::new(Proposition::Implies(
            Box::new(Proposition::ResourceContains {
                parent: Box::new(parent),
                child: Box::new(child.clone()),
            }),
            Box::new(resource_viewable(memory, child)),
        )),
    ))
}

/// Observe the live storage named by one exact held permission. This says
/// nothing about initialization or the value stored in any cell.
pub(crate) fn observe_memory_view(state: &ExecutionState, range: &MemoryRange) -> Option<Theorem> {
    crate::instrumentation::record_deterministic_work(1);
    let resource = Resource::Memory(range.clone());
    if !state
        .resources()
        .contains_exact_representation(&ResourceFact::own(resource.clone()))
        && !state
            .resources()
            .contains_exact_representation(&ResourceFact::View(resource))
    {
        return None;
    }
    Some(Theorem::new(range.loadable_fact(state.memory())))
}
