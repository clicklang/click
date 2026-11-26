// Scaling tests of `src/kernel/primitives/memory_state.rs` (module `initialization_record_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn unwritten_output_preserves_external_runs_without_expanding_their_slots() {
    let mut samples = Vec::new();
    for count in [8u32, 32, 128, 512, 65536] {
        let _session = crate::kernel::VerificationSession::enter();
        let field = OldAddress::symbolic(Variable(924_050));
        let output = OldAddress::symbolic(Variable(924_051));
        let before = SymbolicMemory::new()
            .with_seeded_cells(
                field.clone(),
                1,
                ProgramType::UInt8,
                0,
                count,
                intern_memory(SymbolicMemory::new()),
            )
            .with_uninitialized_object(output.clone(), 4);
        let (after, work) = crate::instrumentation::measure_deterministic_work(|| {
            before.without_possible_aliasing_cells(&output, 1, &PureFactContext::new())
        });
        assert!(after.has_initialized_bytes_at(&field, count));
        assert!(!after.has_initialized_bytes_at(&field, count + 1));
        assert_eq!(after.heap.initialized.len(), 1);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "{samples:?}"
    );
}

#[test]
fn a_declared_object_makes_dropping_its_runs_one_query() {
    // With the declaration's object recorded, a havoc dropping its runs
    // costs the runs, not their slots, whatever the struct count.
    let mut works = Vec::new();
    for count in [1_000u32, 10_000, 100_000] {
        let block = format!("local:record-declared-{count}");
        let memory =
            zero_runs(&block, count, 8).with_initialized_object(&element(&block, 0), count * 8);
        let (havoc, work) =
            crate::instrumentation::measure_deterministic_work(|| loop_havoc(memory, 924_006));
        assert!(havoc.has_initialized_bytes_at(&element(&block, 0), count * 8));
        works.push(work);
    }
    assert!(
        works.windows(2).all(|pair| pair[0] == pair[1]),
        "dropping declared runs cost {works:?} work units"
    );
}

#[test]
fn a_covering_query_scales_with_the_cells_it_crosses() {
    // A read bounded to two elements of an array whose every element is
    // a cached cell costs those two cells, whatever the array's size.
    let mut works = Vec::new();
    for count in [64i64, 512, 4096] {
        let block = format!("local:record-cells-{count}");
        let mut memory =
            SymbolicMemory::new().with_block(block.as_str(), u32::try_from(4 * count).unwrap());
        for index in 0..count {
            memory = memory.store(
                element(&block, index),
                ProgramValue::Int32(OldMachineTerm::constant(1)),
            );
        }
        let index = OldMachineTerm::Variable(Variable(924_008));
        let read = OldAddress {
            base: AddressBase::from(block.as_str()),
            offset: AddressOffset::scale_int32(index.clone(), 4),
        };
        let assumptions = index_between(&index, 7, 8);
        let (covered, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory.has_initialized_bytes_under(&read, 4, &assumptions)
        });
        assert!(covered);
        works.push(work);
    }
    assert!(
        works.windows(2).all(|pair| pair[0] == pair[1]),
        "covering queries cost {works:?} work units"
    );
}

#[test]
fn forgotten_external_initialization_does_not_scan_unrelated_cached_cells() {
    let mut samples = Vec::new();
    for count in [16u32, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let field = OldAddress::symbolic(Variable(924_052));
        let output = OldAddress {
            base: AddressBase::Heap(924_053),
            offset: AddressOffset::constant(0),
        };
        let background = |index| OldAddress {
            base: AddressBase::Heap(925_000 + u64::from(index)),
            offset: AddressOffset::constant(0),
        };
        let mut before =
            SymbolicMemory::new().store(field.clone(), ProgramValue::pointer(OldAddress::null()));
        for index in 0..count {
            before = before.store(
                background(index),
                ProgramValue::Int32(OldMachineTerm::constant(7)),
            );
        }
        let before = before.with_uninitialized_object(output.clone(), 4);
        let (after, work) = crate::instrumentation::measure_deterministic_work(|| {
            before.without_possible_aliasing_cells(&output, 1, &PureFactContext::new())
        });
        assert!(after.known_value(&field).is_none());
        assert!(after.has_initialized_bytes_at(&field, 8));
        assert!(after.known_value(&background(count - 1)).is_some());
        assert!(!after.has_initialized_bytes_at(&output, 1));
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "{samples:?}"
    );
}
