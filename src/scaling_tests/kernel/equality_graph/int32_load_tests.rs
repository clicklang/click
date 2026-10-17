// Scaling tests of `src/kernel/equality_graph/int32_load_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn int32_load_late_merge_and_fork_work_scales_with_affected_applications() {
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = memory();
        let indexed = |index, suffix| Pointer {
            block: "array".into(),
            offset: PointerOffsetTerm::Add(
                Box::new(address(index).offset),
                Box::new(PointerOffsetTerm::Variable(Variable(100 + suffix))),
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
#[ignore = "nightly: 0.7s in the parallel gate"]
fn int32_load_nested_registration_and_late_closure_are_iterative_and_scale() {
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = memory();
        let nested = |mut value| {
            for _ in 0..size {
                value = load(
                    &memory,
                    &Pointer {
                        block: "array".into(),
                        offset: PointerOffsetTerm::scale_int32(value, 4),
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
        let before = CMemory::new();
        let execution = before.with_block("local:raw-read", 8).store(
            CMemory::local_pointer("raw-read"),
            CValue::Int32(0u32.into()),
        );
        let load = |memory: &CMemory| {
            Bitvector32Term::MemoryLoad(
                intern_c_memory_ref(memory),
                Box::new(field.clone()),
                crate::kernel::LoadKind::Bits32,
            )
        };
        let backing = Pointer {
            block: owner.block.clone(),
            offset: PointerOffsetTerm::scale_int32(load(&execution), 4),
        };
        let after = execution.clone().store(
            backing.offset_by_int32_elements(var(88)),
            CValue::Int32(7u32.into()),
        );
        let selected = Pointer {
            block: owner.block.clone(),
            offset: PointerOffsetTerm::scale_int32(load(&after), 4),
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
                &address(950_000 + index),
                4,
                CType::Int32Pointer,
            );
        }
        let field = address(940_061);
        let arena = Pointer::symbolic(Variable(940_062));
        let mut graph = EqualityGraph::default();
        graph.add_equality(&Pointer::loaded_value(&memory, &field), &arena);
        let named_read = |address: &Pointer| {
            let value = Pointer::loaded(address.block.clone(), load(&memory, address, 8), 4);
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
