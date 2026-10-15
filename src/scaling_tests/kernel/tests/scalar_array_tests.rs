// Scaling tests of `src/kernel/tests/scalar_array_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn compact_scalar_arrays_copy_uniform_values_without_expanding_storage_or_work() {
    let mut samples = Vec::new();
    for count in [8, 1024, 1_000_000] {
        let _session = crate::kernel::VerificationSession::enter();
        let (memory, work) = crate::instrumentation::measure_deterministic_work(|| {
            seeded(count)
                .initialize_scalar_array(
                    &pointer("local:array-target", 0),
                    CType::UInt32,
                    count,
                    CValue::pointer(pointer("local:array-source", 0)),
                    true,
                )
                .unwrap()
        });
        assert_eq!(memory.cells.concrete().len(), 0);
        assert_eq!(
            memory
                .cells
                .runs_in_block(&"local:array-source".into())
                .count(),
            1
        );
        assert_eq!(
            memory
                .cells
                .runs_in_block(&"local:array-target".into())
                .count(),
            1
        );
        assert_eq!(
            memory.load(&pointer("local:array-target", i64::from(count - 1) * 4)),
            CExpressionOutcome::Value(CValue::UInt32(Bitvector32Term::Variable(Variable(912_345))))
        );
        assert!(memory.has_initialized_bytes_at(&pointer("local:array-target", 0), count * 4));
        let mutated = memory.clone().store(
            pointer("local:array-source", 0),
            CValue::UInt32(99u32.into()),
        );
        assert_eq!(
            mutated.load(&pointer("local:array-target", 0)),
            memory.load(&pointer("local:array-target", 0))
        );
        samples.push((count, work));
    }
    eprintln!("uniform array initialization/copy (length, work): {samples:?}");
    assert!(
        samples.iter().all(|(_, work)| *work <= samples[0].1 + 32),
        "{samples:?}"
    );
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn scalar_array_copy_after_call_captures_unknown_initialized_values_compactly() {
    let mut samples = Vec::new();
    for count in [8, 1024, 1_000_000] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = pointer("local:array-source", 0);
        let target = pointer("local:array-target", 0);
        let written = CMemoryRange::new_with_element_width(
            source.clone(),
            0u32.into(),
            (count * 4).into(),
            1,
        );
        let after_call = seeded(count).with_call_memory_havoc(
            Variable(912_347),
            &[written],
            &PureFactContext::new(),
            None,
        );
        assert!(after_call.has_initialized_bytes_at(&source, count * 4));
        assert_eq!(after_call.cells.runs_in_block(&source.block).count(), 0);
        let snapshot = intern_c_memory_ref(&after_call);
        let (copied, work) = crate::instrumentation::measure_deterministic_work(|| {
            after_call
                .initialize_scalar_array(
                    &target,
                    CType::UInt32,
                    count,
                    CValue::pointer(source.clone()),
                    true,
                )
                .unwrap()
        });
        let run = copied.cells.runs_in_block(&target.block).next().unwrap();
        assert_eq!(run.source(), &snapshot);
        assert!(
            matches!(run.value_mode(), crate::kernel::primitives::RunValueMode::Copy {
            source_base
        } if source_base == &source)
        );
        assert_eq!(copied.cells.runs_in_block(&target.block).count(), 1);
        assert_eq!(copied.cells.concrete().len(), 0);
        for index in [0, count - 1] {
            let at = pointer("local:array-target", i64::from(index) * 4);
            let held = copied.load(&at);
            assert!(matches!(held, CExpressionOutcome::Value(CValue::UInt32(_))));
            assert_ne!(
                held,
                CExpressionOutcome::Value(CValue::UInt32(Bitvector32Term::Variable(Variable(
                    912_345
                )),))
            );
            let changed = copied.clone().store(
                pointer("local:array-source", i64::from(index) * 4),
                CValue::UInt32(99u32.into()),
            );
            assert_eq!(changed.load(&at), held);
        }
        samples.push((count, work));
    }
    assert!(
        samples.iter().all(|(_, work)| *work <= samples[0].1 + 32),
        "{samples:?}"
    );
}

#[test]
fn compact_array_regions_copy_and_overwrite_preserve_neighbors_and_scale() {
    let mut samples = Vec::new();
    for count in [4, 1024, 1_000_000] {
        let _session = crate::kernel::VerificationSession::enter();
        let bytes = count * 4;
        let source = pointer("local:region-source", 4);
        let target = pointer("local:region-target", 4);
        let context = PureFactContext::new();
        let (memory, work) = crate::instrumentation::measure_deterministic_work(|| {
            let memory = CMemory::new()
                .with_block(source.block.clone(), bytes + 8)
                .with_block(target.block.clone(), bytes + 8)
                .store(
                    pointer("local:region-target", 0),
                    CValue::UInt32(11u32.into()),
                )
                .store(
                    pointer("local:region-target", i64::from(bytes) + 4),
                    CValue::UInt32(17u32.into()),
                )
                .write_scalar_array_region(
                    &source,
                    CType::UInt32,
                    count,
                    CValue::UInt32(7u32.into()),
                    false,
                    false,
                    &context,
                )
                .unwrap()
                .write_scalar_array_region(
                    &target,
                    CType::UInt32,
                    count,
                    CValue::UInt32(99u32.into()),
                    false,
                    false,
                    &context,
                )
                .unwrap();
            memory
                .write_scalar_array_region(
                    &target,
                    CType::UInt32,
                    count,
                    CValue::pointer(source.clone()),
                    true,
                    false,
                    &context,
                )
                .unwrap()
        });
        for (offset, value) in [
            (0, 11),
            (4, 7),
            (i64::from(bytes), 7),
            (i64::from(bytes) + 4, 17),
        ] {
            assert_eq!(
                memory.load(&pointer("local:region-target", offset)),
                CExpressionOutcome::Value(CValue::UInt32(value.into()))
            );
        }
        assert_eq!(memory.cells.concrete().len(), 2);
        assert_eq!(memory.cells.runs_in_block(&target.block).count(), 1);
        assert!(memory.has_initialized_bytes_at(&target, bytes));
        let mutated = memory.store(source, CValue::UInt32(101u32.into()));
        assert_eq!(
            mutated.load(&target),
            CExpressionOutcome::Value(CValue::UInt32(7u32.into()))
        );
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "{samples:?}"
    );
}

#[test]
fn scalar_array_snapshots_preserve_sparse_lanes_without_extent_work() {
    let mut samples = Vec::new();
    for count in [8, 1024, 1_000_000] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = pointer("local:array-source", 0);
        let target = pointer("local:array-target", 0);
        let lane = CValue::UInt32(Bitvector32Term::Variable(Variable(912_346)));
        let memory = seeded(count).store(source.clone(), lane.clone()).store(
            pointer("local:array-source", i64::from(count - 1) * 4),
            CValue::UInt32(17u32.into()),
        );
        let (copied, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory
                .initialize_scalar_array(
                    &target,
                    CType::UInt32,
                    count,
                    CValue::pointer(source.clone()),
                    true,
                )
                .unwrap()
        });
        assert_eq!(copied.cells.concrete().len(), 4);
        assert_eq!(copied.cells.runs_in_block(&target.block).count(), 1);
        assert_eq!(
            copied.load(&target),
            CExpressionOutcome::Value(lane.clone())
        );
        assert_eq!(
            copied.load(&pointer("local:array-target", i64::from(count - 1) * 4)),
            CExpressionOutcome::Value(CValue::UInt32(17u32.into()))
        );
        let changed = copied
            .store(source.clone(), CValue::UInt32(99u32.into()))
            .store(
                pointer("local:array-target", 4),
                CValue::UInt32(18u32.into()),
            );
        assert_eq!(changed.load(&target), CExpressionOutcome::Value(lane));
        assert_eq!(
            changed.load(&pointer("local:array-source", 4)),
            CExpressionOutcome::Value(CValue::UInt32(Bitvector32Term::Variable(Variable(912_345))))
        );
        samples.push((count, work));
    }
    eprintln!("sparse snapshot copy (length, work): {samples:?}");
    assert!(
        samples.iter().all(|(_, work)| *work <= samples[0].1 + 32),
        "{samples:?}"
    );
}

#[test]
fn scalar_array_snapshot_region_does_not_scan_unrelated_sibling_cells() {
    let mut samples = Vec::new();
    for siblings in [1, 64, 2048] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = pointer("local:siblings", 4);
        let target = pointer("local:target", 0);
        let mut memory = CMemory::new()
            .with_block(source.block.clone(), (siblings + 5) * 4)
            .with_block(target.block.clone(), 16)
            .write_scalar_array_region(
                &source,
                CType::UInt32,
                4,
                CValue::UInt32(7u32.into()),
                false,
                false,
                &PureFactContext::new(),
            )
            .unwrap()
            .store(source.clone(), CValue::UInt32(9u32.into()));
        for index in 0..siblings {
            memory = memory.store(
                pointer("local:siblings", i64::from(index + 5) * 4),
                CValue::UInt32(11u32.into()),
            );
        }
        let (copied, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory
                .write_scalar_array_region(
                    &target,
                    CType::UInt32,
                    4,
                    CValue::pointer(source),
                    true,
                    false,
                    &PureFactContext::new(),
                )
                .unwrap()
        });
        assert_eq!(
            copied.load(&target),
            CExpressionOutcome::Value(CValue::UInt32(9u32.into()))
        );
        samples.push((siblings, work));
    }
    assert!(
        samples.iter().all(|(_, work)| *work <= samples[0].1 + 128),
        "{samples:?}"
    );
}
