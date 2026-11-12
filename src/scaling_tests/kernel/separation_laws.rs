use super::*;

#[test]
fn subrange_law_does_not_enumerate_the_interval() {
    for format in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
        let constant = |n| {
            if format == MachineIntegerType::UInt64 {
                MachineTerm::uint64_constant(n)
            } else {
                MachineTerm::constant(n as u32)
            }
        };
        let costs = [4u64, 64, 4096, 1_000_000].map(|length| {
            let _session = crate::kernel::VerificationSession::enter();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::prove_separation_subrange(
                    CPointerValue::new(Pointer::symbolic(Variable(8_390_000)), CType::Int64Pointer),
                    8,
                    format,
                    constant(0),
                    constant(length),
                    constant(1),
                    constant(length - 1),
                )
            });
            work
        });
        assert!(costs[0] > 0);
        assert!(
            costs.iter().all(|cost| *cost == costs[0]),
            "{format:?}: {costs:?}"
        );
    }
}

#[test]
fn elements_laws_do_not_walk_the_index_distance() {
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        for width in [1, 8, 16] {
            let costs = [4i32, 64, 4096, i32::MAX].map(|distance| {
                let _session = crate::kernel::VerificationSession::enter();
                let term = |n: i32| match format {
                    MachineIntegerType::Int32 => MachineTerm::constant(n as u32),
                    _ => MachineTerm::int64_constant(i64::from(n)),
                };
                let base =
                    CPointerValue::new(Pointer::symbolic(Variable(8_390_001)), CType::Int64Pointer);
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    crate::kernel::prove_separation_elements(
                        base.clone(),
                        width,
                        format,
                        term(0),
                        term(distance),
                    )
                });
                // The address law builds the same two addresses.
                let (_, address_work) = crate::instrumentation::measure_deterministic_work(|| {
                    crate::kernel::prove_separation_distinct_elements(
                        base.clone(),
                        width,
                        format,
                        term(0),
                        term(distance),
                    )
                });
                (work, address_work)
            });
            assert!(costs[0].0 > 0 && costs[0].1 > 0);
            assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
        }
    }
}

#[test]
fn conjunction_construction_and_index_keys_do_not_rewalk_prefixes() {
    use std::hash::{Hash, Hasher};
    let costs = [16usize, 32, 64, 128].map(|n| {
        let _session = crate::kernel::VerificationSession::enter();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut expression = CResource::Emp;
            for i in 0..n {
                expression = CResource::star(expression, CResource::Parameter(Variable(i as u64)));
                // Fact indexes hash the new descriptor at each written step.
                let mut key = std::collections::hash_map::DefaultHasher::new();
                expression.hash(&mut key);
                std::hint::black_box(key.finish());
                // A named law must reuse the selected operand, not expand it.
                crate::kernel::prove_resource_law(
                    "click::separation::contains_refl",
                    &[expression.clone()],
                )
                .unwrap();
            }
        });
        work
    });
    assert!(costs[0] > 0);
    for pair in costs.windows(2) {
        assert!(pair[1] <= 3 * pair[0], "{costs:?}");
    }
}

#[test]
fn conjunction_lowering_visits_written_operands_not_ambient_facts() {
    fn cost(n: usize, right_nested: bool, ambient: usize, memory: bool) -> usize {
        let _session = crate::kernel::VerificationSession::enter();
        let mut resource = SpecResource::Value(CResource::Emp);
        for i in 0..n {
            let leaf = SpecResource::Value(if memory {
                CResource::Memory(CMemoryRange::new_with_element_width(
                    Pointer::symbolic(Variable(8_391_000)),
                    0u32.into(),
                    MachineTerm::Variable(Variable(8_392_000 + i as u64)),
                    4,
                ))
            } else {
                CResource::Parameter(Variable(i as u64))
            });
            resource = if right_nested {
                SpecResource::Star(Box::new(leaf), Box::new(resource))
            } else {
                SpecResource::Star(Box::new(resource), Box::new(leaf))
            };
        }
        let mut assumptions = PureFactContext::new();
        for i in 0..ambient {
            assumptions = assumptions.assume_proposition(Proposition::CResourceContains {
                parent: Box::new(CResource::Parameter(Variable(i as u64))),
                child: Box::new(CResource::Parameter(Variable(i as u64 + 1))),
            });
        }
        let proposition = SpecProposition::ResourceSeparate {
            left: resource,
            right: SpecResource::Value(CResource::Emp),
        };
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::spec::lower_spec_proposition_at_state_with_loop_entry(
                &CState::new(),
                &proposition,
                None,
                &assumptions,
                &mut ExecutionBudget::default(),
            )
            .unwrap()
        });
        assert_eq!(paths.len(), 1);
        work
    }
    for (right_nested, memory) in [(false, false), (true, false), (false, true), (true, true)] {
        let costs = [16, 32, 64, 128].map(|n| cost(n, right_nested, 0, memory));
        assert!(costs[0] > 0);
        for pair in costs.windows(2) {
            assert!(pair[1] <= 3 * pair[0], "{costs:?}");
        }
        assert_eq!(
            cost(64, right_nested, 0, memory),
            cost(64, right_nested, 4096, memory)
        );
    }
}

#[test]
fn viewable_restrict_does_not_walk_compositions_or_enumerate_memory() {
    let costs = [4u32, 16, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let mut parent = CResource::Emp;
        for i in 0..size {
            parent = CResource::star(parent, CResource::Parameter(Variable(i as u64)));
        }
        let memory = CMemory::new();
        let range = CResource::Memory(CMemoryRange::new_with_element_width(
            Pointer::symbolic(Variable(8_390_100)),
            0u32.into(),
            size.into(),
            4,
        ));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            prove_viewable_restrict(&memory, parent, CResource::Parameter(Variable(0)));
            prove_viewable_restrict(&memory, range.clone(), range);
        });
        work
    });
    assert!(costs[0] > 0);
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}

#[test]
fn element_containment_does_not_enumerate_its_interval() {
    for format in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
        let constant = |n| {
            if format == MachineIntegerType::UInt64 {
                MachineTerm::uint64_constant(n)
            } else {
                MachineTerm::constant(n as u32)
            }
        };
        let costs = [4u64, 64, 4096, 1_000_000].map(|length| {
            let _session = crate::kernel::VerificationSession::enter();
            crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::prove_separation_contains_element(
                    CPointerValue::new(Pointer::symbolic(Variable(8_390_002)), CType::Int64Pointer),
                    8,
                    format,
                    constant(0),
                    constant(length),
                    constant(length - 1),
                )
            })
            .1
        });
        assert!(costs[0] > 0);
        assert!(
            costs.iter().all(|cost| *cost == costs[0]),
            "{format:?}: {costs:?}"
        );
    }
}
