// Scaling tests of `src/kernel/resource_tracker/tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn truncating_integer_read_collection_is_linear_in_shared_nodes() {
    use crate::kernel::{IntegerTerm, SharedIntegerTerm, Variable};
    for depth in [2usize, 8, 32, 128] {
        let mut term: SharedIntegerTerm = IntegerTerm::var(Variable(91004)).into();
        for _ in 0..depth {
            term = IntegerTerm::TruncatingQuotient(term.clone(), term).into();
        }
        let mut reads = Vec::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            super::super::collect_integer_reads(&term, &mut reads);
        });
        assert!(reads.is_empty());
        assert!(work <= depth + 2, "depth={depth}, work={work}");
    }
}

#[test]
fn branch_join_read_query_does_not_scan_unrelated_cached_cells() {
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let cell = at(block("global:g"), 0);
        let mut before = entry_memory();
        for index in 0..size {
            before = before.store(at(block("global:unrelated"), index * 4), one());
        }
        let first = before.clone().store(at(block("global:h"), 0), one());
        let second = before.clone().store(
            at(block("global:h"), 0),
            ProgramValue::Int32(OldMachineTerm::constant(2)),
        );
        let joined = first
            .clone()
            .with_interface_memory_havoc(
                Variable(981003),
                &std::collections::BTreeSet::<crate::kernel::AddressBase>::new(),
                &[&first, &second],
            )
            .unwrap();
        // Warm only the common prefix. The query below must inspect the
        // new branch delta, not repeat all of that prefix's work.
        let expected = last_same_version_point(
            TrackedResource::Cell {
                pointer: &cell,
                bytes: crate::kernel::AccessExtent::from(8),
            },
            &point(&before),
        );
        let (answer, work) = crate::instrumentation::measure_deterministic_work(|| {
            last_same_version_point(
                TrackedResource::Cell {
                    pointer: &cell,
                    bytes: crate::kernel::AccessExtent::from(8),
                },
                &point(&joined),
            )
        });
        assert_eq!(answer, expected);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "selected read work: {samples:?}"
    );
}

#[test]
fn branch_join_nested_naming_work_tracks_new_branches() {
    let cell = at(block("global:g"), 0);
    let mut memory = entry_memory();
    let expected = last_same_version_point(
        TrackedResource::Cell {
            pointer: &cell,
            bytes: crate::kernel::AccessExtent::from(8),
        },
        &point(&memory),
    );
    let mut samples = Vec::new();
    for index in 0..32 {
        let left = memory.clone().store(
            at(block("global:h"), 0),
            ProgramValue::Int32(OldMachineTerm::constant(index * 2)),
        );
        let right = memory.clone().store(
            at(block("global:h"), 0),
            ProgramValue::Int32(OldMachineTerm::constant(index * 2 + 1)),
        );
        memory = left
            .clone()
            .with_interface_memory_havoc(
                Variable(981030 + u64::from(index)),
                &std::collections::BTreeSet::<crate::kernel::AddressBase>::new(),
                &[&left, &right],
            )
            .unwrap();
        let (answer, work) = crate::instrumentation::measure_deterministic_work(|| {
            last_same_version_point(
                TrackedResource::Cell {
                    pointer: &cell,
                    bytes: crate::kernel::AccessExtent::from(8),
                },
                &point(&memory),
            )
        });
        assert_eq!(answer, expected);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "each new branch should pay only for its own two arms: {samples:?}"
    );
}

#[test]
fn adjacent_cell_preservation_costs_only_the_selected_edge() {
    // An explicit chain names the previous state at every store. Each
    // query establishes exactly that adjacent equality, never its prefix.
    let mut samples = Vec::new();
    for size in [16i64, 64, 256] {
        let cell = at(block("global:g"), 0);
        let mut memory = entry_memory().store(cell.clone(), one());
        let assumptions = PureFactContext::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                let previous = intern_memory(memory.clone());
                memory = memory
                    .clone()
                    .store(at(block("global:unrelated"), index * 4), one());
                let source = cell_source::memory_dag_cell_source(
                    &intern_memory(memory.clone()),
                    &cell,
                    4,
                    &assumptions,
                    false,
                )
                .expect("no lookup of this cell is in progress");
                let cell_source::MemoryDagCell::Unwritten { node, path } = source else {
                    panic!("one selected edge cannot recover the older stored value");
                };
                assert_eq!(node, previous);
                assert_eq!(path.len(), 1);
                assert_eq!(
                    path[0].justification,
                    cell_source::MemoryDagHopJustification::StoreDistinctBlocks
                );
            }
        });
        samples.push((size, work));
    }
    let (small, small_work) = samples[0];
    let (large, large_work) = samples[samples.len() - 1];
    assert!(
        large_work * (small as usize) <= small_work * (large as usize) * 2,
        "repeated cell walk work: {samples:?}"
    );
}

#[test]
fn retained_cell_stops_scale_with_new_steps_and_ignore_other_names() {
    let mut samples = Vec::new();
    for size in [8, 16, 32, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let cell = at(block("global:g"), 0);
        let mut memory = entry_memory().store(cell.clone(), one());
        let expected =
            last_same_named_cell(&cell, crate::kernel::AccessExtent::from(4), &point(&memory))
                .unwrap();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for i in 0..size {
                memory = memory.clone().store(
                    at(block("local:f:i"), 0),
                    ProgramValue::Int32(OldMachineTerm::constant(i)),
                );
                let here = point(&memory);
                assert_eq!(
                    last_same_named_cell(&cell, crate::kernel::AccessExtent::from(4), &here),
                    Some(expected.clone())
                );
                let (again, repeat_work) =
                    crate::instrumentation::measure_deterministic_work(|| {
                        last_same_named_cell(&cell, crate::kernel::AccessExtent::from(4), &here)
                    });
                assert_eq!(again, Some(expected.clone()));
                assert_eq!(repeat_work, 0);
            }
        });
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= 2 * pair[0] + 32, "retained stops: {samples:?}");
    }
    for size in [0, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = entry_memory();
        for i in 0..size {
            last_same_named_cell(
                &at(block("global:g"), i * 4),
                crate::kernel::AccessExtent::from(4),
                &point(&memory),
            );
        }
        let cell = at(block("global:h"), 0);
        let here = point(&memory);
        let expected = last_same_named_cell(&cell, crate::kernel::AccessExtent::from(4), &here);
        let (answer, work) = crate::instrumentation::measure_deterministic_work(|| {
            last_same_named_cell(&cell, crate::kernel::AccessExtent::from(4), &here)
        });
        assert_eq!(answer, expected);
        assert_eq!(work, 0, "unrelated names: {size}");
    }
}

#[test]
fn fresh_cell_offsets_share_the_whole_block_version_prefix() {
    let samples = [8usize, 16, 32, 64].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let entry = intern_memory(SymbolicMemory::new());
        let mut memory = entry.memory().clone();
        for index in 0..size {
            memory = memory.store(at(AddressBase::Temporary(998_980 + index as u64), 0), one());
        }
        let current = point(&memory);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                let pointer = at(AddressBase::ExternalArgument, index as i64 * 4);
                assert_eq!(
                    last_same_version_point(
                        TrackedResource::Cell {
                            pointer: &pointer,
                            bytes: crate::kernel::AccessExtent::from(4)
                        },
                        &current
                    )
                    .unwrap()
                    .shared_memory(),
                    &entry,
                );
            }
        });
        work
    });
    assert!(samples[0] > 0);
    assert!(
        samples
            .windows(3)
            .all(|p| p[2] - p[1] <= 2 * (p[1] - p[0]) + 8),
        "fresh offsets after separate stores: {samples:?}"
    );
}

#[test]
fn forgotten_cell_recovery_ignores_older_history_and_unrelated_cache_entries() {
    use super::super::cell_source::{CellWalkStop, memory_dag_cell_source_with_stop};
    crate::kernel::memory_history::with_extended_dag_bridging(|| {
        let mut samples = Vec::new();
        for size in [4, 16, 64] {
            let pointer = at(block("global:g"), 0);
            let assumptions = PureFactContext::new();
            let mut before = SymbolicMemory::new()
                .with_block(block("global:g"), 4)
                .with_block(block("global:h"), (size * 4) as u32);
            for index in 0..size {
                before = before.store(pointer.clone(), one());
                before = before.store(at(block("global:h"), index * 4), one());
            }
            let forgotten = intern_memory(before.without_possible_aliasing_cells(
                &pointer.offset_by_bytes(1),
                1,
                &assumptions,
            ));
            let ((cell, stop), work) = crate::instrumentation::measure_deterministic_work(|| {
                memory_dag_cell_source_with_stop(&forgotten, &pointer, 4, &assumptions, true)
                    .unwrap()
            });
            assert_eq!(stop, CellWalkStop::RetainedValue);
            assert_eq!(
                cell.resolved_value(&pointer, crate::kernel::LoadKind::Int32),
                Some(one())
            );
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work == samples[0]),
            "{samples:?}"
        );
    });
}

#[test]
fn loop_kept_pointer_frame_ignores_unrelated_owners_and_ambiguous_buckets() {
    use crate::kernel::{CallKeptRanges, ResourceContext, ResourceFact};
    let mut samples = Vec::new();
    for size in [4u32, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Address::symbolic(Variable(980115));
        let ambiguous = Address::symbolic(Variable(980116));
        let range = |base: Address, count: u32| {
            MemoryRange::new_with_element_width(base, 0u32.into(), count.into(), 1)
        };
        let mut owners = ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own_memory(range(field.clone(), 8)));
        for index in 0..size {
            owners = owners
                .unchecked_with_fact(ResourceFact::own_memory(range(
                    Address::symbolic(Variable(981000 + u64::from(index))),
                    8,
                )))
                .unchecked_with_fact(ResourceFact::own_memory(range(
                    ambiguous.clone(),
                    index + 16,
                )));
        }
        let base = SymbolicMemory::new();
        let before = intern_memory(base.clone());
        let after = intern_memory(base.with_loop_memory_havoc_preserving_frame(
            Variable(980117),
            &std::collections::BTreeSet::new(),
            Some(&[range(field.clone(), 128), range(ambiguous.clone(), 128)]),
            None,
            Some(CallKeptRanges::new(owners, vec![], None)),
        ));
        let context = PureFactContext::new();
        let query = |address: &Address| {
            crate::kernel::memory_history::complete_pointer_reads_equal_across_frame(
                &Address::loaded_value(&before, address),
                &Address::loaded_value(&after, address),
                &context,
            )
        };
        let (hit, hit_work) = crate::instrumentation::measure_deterministic_work(|| query(&field));
        let (miss, miss_work) =
            crate::instrumentation::measure_deterministic_work(|| query(&ambiguous));
        assert!(hit);
        assert!(!miss, "an ambiguous supplier bucket must not be searched");
        samples.push((hit_work, miss_work));
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "{samples:?}"
    );
}

#[test]
fn cold_cell_source_lookup_does_not_search_older_stores() {
    let mut costs = Vec::new();
    for size in [4i64, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let cell = at(block("global:kept"), 0);
        let mut memory = entry_memory().store(cell.clone(), one());
        for index in 0..size {
            memory = memory.store(at(block("global:other"), index * 4), one());
        }
        let memory = intern_memory(memory);
        let facts = PureFactContext::new();
        let (answer, work) = crate::instrumentation::measure_deterministic_work(|| {
            cell_source::memory_dag_cell_source(&memory, &cell, 4, &facts, false).unwrap()
        });
        assert!(
            matches!(answer, cell_source::MemoryDagCell::Unwritten { ref path, .. } if path.len() == 1)
        );
        costs.push(work);
        // N fresh cell queries after N stores must be linear in N, including
        // cells whose value was never stored. Each query is cold for its address.
        let (_, total) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                let answer = cell_source::memory_dag_cell_source(
                    &memory,
                    &at(block("global:kept"), index * 4),
                    4,
                    &facts,
                    false,
                )
                .unwrap();
                assert!(
                    matches!(answer, cell_source::MemoryDagCell::Unwritten { ref path, .. }
                    if path.len() == 1)
                );
            }
        });
        assert_eq!(total, size as usize * work);
        // The same history can be followed when the caller explicitly names
        // a hop budget. This control exposes the work the default query avoids.
        let (answer, walked) = crate::instrumentation::measure_deterministic_work(|| {
            cell_source::memory_dag_cell_source_with_hop_limit(
                &memory,
                &cell,
                4,
                &facts,
                size as usize + 1,
            )
            .unwrap()
        });
        assert!(
            matches!(answer, cell_source::MemoryDagCell::Stored { value, .. } if value == one())
        );
        assert!(walked >= size as usize, "size={size}: {walked}");
        let latest = intern_memory(
            memory
                .memory()
                .clone()
                .store(cell.clone(), ProgramValue::Int32(2u32.into())),
        );
        assert!(
            matches!(cell_source::memory_dag_cell_source(&latest, &cell, 4, &facts, false), Some(cell_source::MemoryDagCell::Stored { value, .. }) if value == ProgramValue::Int32(2u32.into()))
        );
        assert!(!matches!(
            cell_source::memory_dag_cell_source(&latest, &cell, 8, &facts, false),
            Some(cell_source::MemoryDagCell::Stored { .. })
        ));
    }
    assert!(
        costs[0] > 0 && costs.iter().all(|cost| *cost == costs[0]),
        "{costs:?}"
    );
}

#[test]
fn shared_pointer_resource_read_collection_visits_each_node_once() {
    use crate::kernel::{
        KernelTerm, KernelTermExport, MachineBinaryOp, MachineOperandView as V,
        SharedMachineIntegerTerm as S,
    };
    let mut costs = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Address::symbolic(crate::kernel::Variable(1081601));
        let memory = intern_memory(SymbolicMemory::new().store(address.clone(), one()));
        let read = OldMachineTerm::read_named(
            ProgramPoint::at(&memory),
            Box::new(address),
            crate::kernel::LoadKind::Int32,
        );
        let mut root =
            KernelTerm::retained_machine_operand(MachineIntegerType::Int32, V::Old(&read));
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
        }
        let offset = OldAddressOffset::Int32Scaled {
            value: S::from_shared(MachineIntegerType::Int32, root).unwrap(),
            byte_width: 4,
        };
        let mut reads = Vec::new();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            collect_offset_reads(&offset, &mut reads)
        });
        assert_eq!(reads.len(), 1);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        costs.push(work);
    }
    assert!(costs[1] <= costs[0] * 5 + 10, "{costs:?}");
    assert!(costs[2] <= costs[1] * 5 + 10, "{costs:?}");
}

#[test]
fn shared_conditional_guard_reads_keep_state_identity_in_linear_work() {
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelTermImport, KernelType, MachineOperandView, Variable,
        VerificationSession,
    };
    for size in [16usize, 64, 256] {
        let _session = VerificationSession::enter();
        let memory = intern_memory(SymbolicMemory::new().with_declared_scalar_block(
            block("global:g"),
            4,
            ProgramType::Int32,
        ));
        let pointer = at(block("global:g"), 0);
        crate::kernel::eval::record_load_access_width(memory.memory(), &pointer, 4);
        let guard = OldConditionTerm::equal(
            OldMachineTerm::read_named(
                ProgramPoint::at(&memory),
                Box::new(pointer.clone()),
                LoadKind::Int32,
            ),
            OldMachineTerm::constant(0),
        );
        let guard = KernelTermImport::default().condition(&guard);
        let mut root =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(998201));
        for _ in 0..size {
            root = KernelTerm::machine_if_shared(
                MachineIntegerType::Int32,
                [guard.clone(), root.clone(), root],
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let mut reads = Vec::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            super::super::collect_operand_reads(MachineOperandView::Shared(&root), &mut reads);
        });
        assert_eq!(reads.len(), 1);
        assert_eq!(
            reads[0].resource,
            OwnedResource::Cell {
                pointer,
                bytes: crate::kernel::AccessExtent::from(4)
            }
        );
        assert_eq!(reads[0].point, ProgramPoint::at(&memory));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work <= size * 32 + 16, "size={size}, work={work}");
    }
}

/// Naming a cell on a path visits the points back to the store that wrote
/// it, not the path before that store.
#[test]
fn a_path_version_costs_the_points_after_the_cells_last_store() {
    let mut samples = Vec::new();
    for earlier in [10u32, 100, 1_000] {
        let mut stores = vec![("other", 0u32); earlier as usize];
        stores.push(("slot", 1));
        stores.extend([("other", 2), ("other", 3), ("other", 4)]);
        let states = path_of_stores(&start_with(&["slot", "other"]), &stores);
        let reader = states.last().unwrap();
        clear_version_memos();
        let (version, work) =
            crate::instrumentation::measure_deterministic_work(|| version_on_path(reader, "slot"));
        assert_eq!(version, states[earlier as usize].program_point().id());
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "naming grew with the path before the store: {samples:?}"
    );
}

#[test]
fn cold_static_array_versions_ignore_disjoint_call_history() {
    let _session = crate::kernel::VerificationSession::enter();
    let written = block("global:written");
    let ranges = [MemoryRange::new(
        at(written.clone(), 0),
        0u32.into(),
        4u32.into(),
    )];
    let facts = PureFactContext::new();

    for size in [4, 16, 64, 128] {
        let mut memory = SymbolicMemory::new().with_block(written.clone(), 4);
        let mut arrays = Vec::new();
        for index in 0..size {
            let array = block(&format!("global:array_{index}"));
            memory = memory.with_block(array.clone(), 4);
            arrays.push((array, point(&memory).shared_memory().arena_id()));
        }
        for index in 0..size {
            let identity = Variable(100_000 + size as u64 * 128 + index as u64);
            memory = memory.with_storage_memory_havoc(identity, &ranges, &facts);
        }
        let current = point(&memory);
        assert_eq!(
            last_same_version_point(TrackedResource::Block(&written), &current),
            Some(current.clone())
        );

        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for (array, expected) in &arrays {
                let (version, work) = crate::instrumentation::measure_deterministic_work(|| {
                    last_same_version_point(TrackedResource::Block(array), &current)
                        .expect("static array version")
                });
                assert_eq!(version.shared_memory().arena_id(), *expected);
                assert_eq!(work, 1, "cold lookup after {size} disjoint calls");
            }
        });
        assert_eq!(work, size, "one cold lookup for each of {size} arrays");
    }
}

/// The legacy naming walk's cost for a cell no store wrote is the stores
/// into its block since that block's last version: the block-prefix jump
/// stops at the first of them, and the memo is keyed by the cell. Reading a
/// fresh cell after each of `n` stores into one block therefore costs
/// quadratic work in total. Program-point versions replace this walk
/// (`roadmap/smart-tactics.md`, "Program-point memory migration"); a step
/// must not depend on it. This records the growth so that deleting the walk
/// deletes this test, and a change that hides the growth while keeping the
/// walk fails here.
#[test]
fn legacy_walk_naming_of_fresh_cells_still_grows_with_same_block_stores() {
    for base in [
        AddressBase::ExternalArgument,
        block("local:f:buffer"),
        AddressBase::Heap(77),
    ] {
        let samples = [16usize, 32, 64, 128].map(|size| {
            let _session = crate::kernel::VerificationSession::enter();
            let mut memory = entry_memory();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for index in 0..size {
                    memory = memory
                        .clone()
                        .store(at(base.clone(), index as i64 * 4), one());
                    let fresh = at(base.clone(), (size + index) as i64 * 4);
                    let version = last_same_version_point(
                        TrackedResource::Cell {
                            pointer: &fresh,
                            bytes: crate::kernel::AccessExtent::from(4),
                        },
                        &point(&memory),
                    );
                    assert!(version.is_some());
                }
            });
            work
        });
        // Per doubling, n log n grows by a falling factor (2.5, 2.4, 2.33
        // from 16); quadratic work grows by a factor rising toward 4.
        let growth = samples
            .windows(2)
            .map(|pair| pair[1] as f64 / pair[0] as f64)
            .collect::<Vec<_>>();
        assert!(
            growth.windows(2).all(|pair| pair[1] > pair[0]) && growth[2] > 3.0,
            "{base:?}: the legacy walk no longer grows with same-block stores: \
             {samples:?}, growth {growth:?}"
        );
    }
}
