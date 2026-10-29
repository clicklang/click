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
            CValue::Int32(Bitvector32Term::Constant(2)),
        );
        let joined = first
            .clone()
            .with_interface_memory_havoc(
                Variable(981003),
                &std::collections::BTreeSet::<crate::kernel::PointerBlock>::new(),
                &[&first, &second],
            )
            .unwrap();
        // Warm only the common prefix. The query below must inspect the
        // new branch delta, not repeat all of that prefix's work.
        let expected = last_same_point(
            Resource::Cell {
                pointer: &cell,
                bytes: 8,
            },
            &point(&before),
        );
        let (answer, work) = crate::instrumentation::measure_deterministic_work(|| {
            last_same_point(
                Resource::Cell {
                    pointer: &cell,
                    bytes: 8,
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
    let expected = last_same_point(
        Resource::Cell {
            pointer: &cell,
            bytes: 8,
        },
        &point(&memory),
    );
    let mut samples = Vec::new();
    for index in 0..32 {
        let left = memory.clone().store(
            at(block("global:h"), 0),
            CValue::Int32(Bitvector32Term::Constant(index * 2)),
        );
        let right = memory.clone().store(
            at(block("global:h"), 0),
            CValue::Int32(Bitvector32Term::Constant(index * 2 + 1)),
        );
        memory = left
            .clone()
            .with_interface_memory_havoc(
                Variable(981030 + u64::from(index)),
                &std::collections::BTreeSet::<crate::kernel::PointerBlock>::new(),
                &[&left, &right],
            )
            .unwrap();
        let (answer, work) = crate::instrumentation::measure_deterministic_work(|| {
            last_same_point(
                Resource::Cell {
                    pointer: &cell,
                    bytes: 8,
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
fn a_fact_aware_cell_walk_resumes_the_memoized_version_walk() {
    // Stepping asks about a cell again after each statement. A fact-aware
    // walk that resumes the memoized version walk pays for each statement's
    // own step, so asking after every one of `size` unrelated stores costs
    // work linear in `size`, not one full walk per statement.
    let mut samples = Vec::new();
    for size in [16i64, 64, 256] {
        let cell = at(block("global:g"), 0);
        let mut memory = entry_memory().store(cell.clone(), one());
        let assumptions = PureFactContext::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                memory = memory
                    .clone()
                    .store(at(block("global:unrelated"), index * 4), one());
                let source = cell_source::memory_dag_cell_source(
                    &intern_c_memory(memory.clone()),
                    &cell,
                    4,
                    &assumptions,
                    false,
                )
                .expect("no lookup of this cell is in progress");
                assert!(matches!(source, cell_source::MemoryDagCell::Stored { .. }));
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
        let expected = last_same_named_cell(&cell, 4, &point(&memory)).unwrap();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for i in 0..size {
                memory = memory.clone().store(
                    at(block("local:f:i"), 0),
                    CValue::Int32(Bitvector32Term::Constant(i)),
                );
                let here = point(&memory);
                assert_eq!(
                    last_same_named_cell(&cell, 4, &here),
                    Some(expected.clone())
                );
                let (again, repeat_work) =
                    crate::instrumentation::measure_deterministic_work(|| {
                        last_same_named_cell(&cell, 4, &here)
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
            last_same_named_cell(&at(block("global:g"), i * 4), 4, &point(&memory));
        }
        let cell = at(block("global:h"), 0);
        let here = point(&memory);
        let expected = last_same_named_cell(&cell, 4, &here);
        let (answer, work) = crate::instrumentation::measure_deterministic_work(|| {
            last_same_named_cell(&cell, 4, &here)
        });
        assert_eq!(answer, expected);
        assert_eq!(work, 0, "unrelated names: {size}");
    }
}

#[test]
fn fresh_cell_offsets_share_the_whole_block_version_prefix() {
    let samples = [8usize, 16, 32, 64].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let entry = intern_c_memory(CMemory::new());
        let mut memory = entry.memory().clone();
        for index in 0..size {
            memory = memory.store(
                at(PointerBlock::Temporary(998_980 + index as u64), 0),
                one(),
            );
        }
        let current = point(&memory);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                let pointer = at(PointerBlock::ExternalArgument, index as i64 * 4);
                assert_eq!(
                    last_same_point(
                        Resource::Cell {
                            pointer: &pointer,
                            bytes: 4
                        },
                        &current
                    )
                    .unwrap()
                    .snapshot(),
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
    crate::kernel::memory_provenance::with_extended_dag_bridging(|| {
        let mut samples = Vec::new();
        for size in [4, 16, 64] {
            let pointer = at(block("global:g"), 0);
            let assumptions = PureFactContext::new();
            let mut before = CMemory::new()
                .with_block(block("global:g"), 4)
                .with_block(block("global:h"), (size * 4) as u32);
            for index in 0..size {
                before = before.store(pointer.clone(), one());
                before = before.store(at(block("global:h"), index * 4), one());
            }
            let forgotten = intern_c_memory(before.without_possible_aliasing_cells(
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
