// Scaling tests of `src/kernel/equality_graph/int32_load_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn int32_load_late_merge_and_fork_work_scales_with_affected_applications() {
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = memory();
        let indexed = |index, suffix| Address {
            base: "array".into(),
            offset: AddressOffset::Add(
                Box::new(address(index).offset),
                Box::new(AddressOffset::Variable(Variable(100 + suffix))),
            ),
        };
        let mut graph = EqualityGraph::default();
        for i in 0..size {
            graph.add_int32_equality(&load(&memory, &indexed(1, i), 4), &var(10_000 + i));
            graph.add_int32_equality(&load(&memory, &indexed(2, i), 4), &var(20_000 + i));
        }
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                graph.add_int32_equality(&var(1), &var(2));
                for i in 0..size {
                    assert!(graph.are_int32_equal(&var(10_000 + i), &var(20_000 + i)));
                }
            })
        });
        assert!(work < 200 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 1500 * size as usize * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for i in 0..size {
                    let mut branch = graph.clone();
                    branch.add_int32_equality(&var(30_000 + i), &var(1));
                    let fresh = load(&memory, &indexed(30_000 + i, 0), 4);
                    assert!(branch.are_int32_equal(&fresh, &var(10_000)));
                }
            })
        });
        assert!(work < 250 * size as usize, "size={size}, fork work={work}");
        assert!(
            map_work < 1500 * size as usize * (size.ilog2() as usize + 1),
            "size={size}, fork map work={map_work}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn int32_load_nested_registration_and_late_closure_are_iterative_and_scale() {
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = memory();
        let nested = |mut value| {
            for _ in 0..size {
                value = load(
                    &memory,
                    &Address {
                        base: "array".into(),
                        offset: AddressOffset::scale_int32(value, 4),
                    },
                    4,
                );
            }
            value
        };
        let left = nested(var(1));
        let right = nested(var(2));
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let mut graph = EqualityGraph::default();
                assert!(!graph.are_int32_equal(&left, &right));
                graph.add_int32_equality(&var(1), &var(2));
                assert!(graph.are_int32_equal(&left, &right));
            })
        });
        assert!(work < 300 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 2000 * size as usize * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
    }
}

#[test]
fn raw_read_address_registration_does_not_walk_memory_history() {
    let mut baseline = None;
    for size in [0u64, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let owner = address(87);
        let field = owner.offset_by_bytes(8);
        let before = SymbolicMemory::new();
        let execution = before.with_block("local:raw-read", 8).store(
            SymbolicMemory::local_pointer("raw-read"),
            ProgramValue::Int32(0u32.into()),
        );
        let load = |memory: &SymbolicMemory| {
            OldMachineTerm::read_named(
                ProgramPoint::at(&(intern_memory_ref(memory))),
                Box::new(field.clone()),
                crate::kernel::LoadKind::Int32,
            )
        };
        let backing = Address {
            base: owner.base.clone(),
            offset: AddressOffset::scale_int32(load(&execution), 4),
        };
        let after = execution.clone().store(
            backing.offset_by_int32_elements(var(88)),
            ProgramValue::Int32(7u32.into()),
        );
        let selected = Address {
            base: owner.base.clone(),
            offset: AddressOffset::scale_int32(load(&after), 4),
        };
        let mut graph = EqualityGraph::default();
        for extra in 0..size {
            graph.add_int32_equality(&var(10_000 + 2 * extra), &var(10_001 + 2 * extra));
        }
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            let class = graph
                .address_class(&selected)
                .expect("register the selected read address");
            assert_eq!(graph.address_class(&selected), Some(class));
        });
        let first = *baseline.get_or_insert(work);
        assert!(
            work <= first + 64 && work <= 1024,
            "size={size}, work={work}, baseline={first}"
        );
    }
}

#[test]
fn nested_named_pointer_reads_ignore_unrelated_definitions() {
    let costs = [16u64, 64, 256, 1024].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = memory();
        for index in 0..size {
            memory.memory().symbolic_pointer_load(
                None,
                &address(950_000 + index),
                ProgramType::Int32Pointer,
            );
        }
        let field = address(940_061);
        let arena = Address::symbolic(Variable(940_062));
        let mut graph = EqualityGraph::default();
        graph.add_equality(&Address::loaded_value(&memory, &field), &arena);
        let named_read = |address: &Address| {
            let value = Address::loaded(&load(&memory, address, 8)).unwrap();
            graph.register_pointer_read_definition(&value, &memory, address);
            value
        };
        let named_arena = named_read(&field);
        let direct = named_read(&arena.offset_by_bytes(8));
        let indirect = named_read(&named_arena.offset_by_bytes(8));
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            let direct = direct.offset_by_elements(var(940_063), 4);
            let indirect = indirect.offset_by_elements(var(940_063), 4);
            graph.are_int32_equal(&load(&memory, &direct, 4), &load(&memory, &indirect, 4))
        });
        assert!(equal);
        work
    });
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] + 128),
        "{costs:?}"
    );
}

#[test]
fn zero_index_read_condition_ignores_unrelated_read_predicates() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = memory();
        let mut context = PureFactContext::new();
        for index in 0..size {
            let left = load(&memory, &address(950_000 + 2 * index), 4);
            let right = load(&memory, &address(950_001 + 2 * index), 4);
            context = context.assume_condition(ConditionTerm::signed_less_than(left, right), true);
        }
        let base = address(960_000);
        let index = var(960_001);
        let direct = load(&memory, &base, 4);
        let indexed = load(&memory, &base.offset_by_elements(index.clone(), 4), 4);
        let next = load(
            &memory,
            &base.offset_by_elements(OldMachineTerm::add(index.clone(), 1u32.into()), 4),
            4,
        );
        context =
            context.assume_condition(ConditionTerm::signed_less_than(next.clone(), indexed), true);
        let target = ConditionTerm::signed_less_than(next, direct);
        let (answer, work) = crate::instrumentation::measure_deterministic_work(|| {
            let context = context.assume_condition(ConditionTerm::equal(index, 0u32.into()), true);
            crate::kernel::reasoning::decide_with_facts(&context, &ExecutionFacts::new(), &target)
        });
        assert_eq!(answer, Some(true));
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "{samples:?}"
    );
}

/// An 8- or 16-bit read of a canonical projection is joined to the same read
/// of its recorded source by one indexed edge (`Node::NarrowRead`), as a
/// four-byte read is: deciding that the two reads are one value costs the
/// same work however many stores the source's history holds. A walk from
/// the projection back through that history would grow with it.
#[test]
fn narrow_read_projection_edge_does_not_walk_memory_history() {
    use crate::kernel::{CompareRelation, ConditionTerm, LoadKind, MachineIntegerType};
    for (kind, format, bytes) in [
        (LoadKind::UInt8, MachineIntegerType::UInt8, 1),
        (LoadKind::Int16, MachineIntegerType::Int16, 2),
    ] {
        let mut baseline = None;
        for size in [0u64, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut history = SymbolicMemory::new().with_block("array", 4096);
            for index in 0..size {
                history = history.store(
                    address(500_000 + index),
                    ProgramValue::Int32(OldMachineTerm::constant(index as u32)),
                );
            }
            let source = intern_memory(history.clone());
            let projected = intern_memory(history.with_block("local:projection", 1));
            let cell = address(1);
            crate::kernel::reasoning::record_canonical_load_projection(&source, &projected, &cell);
            let read = |memory: &SharedMemory| {
                OldMachineTerm::Variable(crate::kernel::eval::load_variable_for_exact_cell(
                    memory, &cell, kind, bytes,
                ))
            };
            let equal = ConditionTerm::Compare {
                format,
                relation: CompareRelation::Equal,
                left: Box::new(read(&projected)),
                right: Box::new(read(&source)),
            };
            let graph = EqualityGraph::default();
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut state = graph.state.lock().expect("equality graph");
                assert!(state.terms.knows_condition(&equal, true), "{kind:?}");
            });
            let first = *baseline.get_or_insert(work);
            assert!(
                work == first && work <= 1024,
                "{kind:?}: size={size}, work={work}, baseline={first}"
            );
        }
    }
}

/// R-mem at 16 and 128 bits: registering a signed read costs registering
/// a read plus what the written sign cast of its cell's unsigned read
/// costs, and one union, the same at every size, as the graph's unrelated classes and the class of the read's
/// address grow. A relation that looked for its partner read among the
/// graph's reads, or walked the address class, would grow with them.
#[test]
fn registering_a_signed_16_or_128_bit_read_costs_what_its_unsigned_read_costs() {
    use crate::kernel::{CarrierWidth as W, LoadKind as K, MachineIntegerType as M};
    for (signed_kind, unsigned_kind, from, to, width, bytes) in [
        (K::Int16, K::UInt16, M::UInt16, M::Int16, W::Bits16, 2),
        (K::Int128, K::UInt128, M::UInt128, M::Int128, W::Bits128, 16),
    ] {
        let mut samples = Vec::new();
        for size in [4_u64, 64, 512] {
            let _session = crate::kernel::VerificationSession::enter();
            let memory = memory();
            let read = |kind| {
                OldMachineTerm::Variable(crate::kernel::eval::load_variable_for_exact_cell(
                    &memory,
                    &address(1),
                    kind,
                    bytes,
                ))
            };
            let (signed, unsigned) = (read(signed_kind), read(unsigned_kind));
            let graph = EqualityGraph::default();
            {
                let mut state = graph.state.lock().expect("equality graph");
                for index in 0..size {
                    // Unrelated classes, and a growing class of the address.
                    state.terms.add_typed_equality(
                        width,
                        &var(600_000 + index),
                        &var(700_000 + index),
                    );
                    state
                        .terms
                        .add_int32_equality(&var(1), &var(800_000 + index));
                }
            }
            let measure = |term: &OldMachineTerm| {
                let branch = graph.clone();
                let mut state = branch.state.lock().expect("equality graph");
                crate::instrumentation::measure_deterministic_work(|| {
                    state.terms.register_typed(width, term)
                })
                .1
            };
            let written = OldMachineTerm::machine_integer_cast(from, to, unsigned.clone());
            // Warm the session's read observations, so each sample below is
            // the graph's own work.
            for term in [&unsigned, &signed, &written] {
                measure(term);
            }
            let unsigned_units = measure(&unsigned);
            let signed_units = measure(&signed);
            let written_units = measure(&written);
            // The signed read's own registration costs what the unsigned
            // read's does; its relation costs what the written cast of the
            // unsigned read costs, plus its queue entry and one union.
            assert!(
                signed_units <= unsigned_units + written_units + 8,
                "{signed_kind:?}: size={size}, signed {signed_units}, \
                 unsigned {unsigned_units}, written cast {written_units}"
            );
            samples.push((unsigned_units, signed_units, written_units));
        }
        assert!(
            samples.iter().all(|sample| *sample == samples[0]),
            "{signed_kind:?}: (unsigned, signed, written cast) work grew: {samples:?}"
        );
    }
}
