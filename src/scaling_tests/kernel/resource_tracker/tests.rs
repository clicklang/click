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
