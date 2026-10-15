//! External copies capture immutable typed bytes without allocating one cell per lane.
use super::*;

fn external(id: u64) -> Pointer {
    Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(id)), 4),
    }
}
fn copy(memory: CMemory, target: &Pointer, source: &Pointer, count: u32) -> CMemory {
    memory
        .write_scalar_array_region(
            target,
            CType::UInt32,
            count,
            CValue::pointer(source.clone()),
            true,
            false,
            &PureFactContext::new(),
        )
        .unwrap()
}
fn typed_load(memory: &CMemory, pointer: &Pointer) -> CValue {
    match memory.load(pointer) {
        CExpressionOutcome::Value(value) => value,
        _ => CValue::UInt32(crate::kernel::eval::canonical_form_of_load(
            crate::kernel::intern_c_memory(memory.clone()),
            pointer.clone(),
            crate::kernel::primitives::LoadKind::Bits32,
        )),
    }
}

#[test]
fn external_array_sparse_copies_forward_snapshots_and_preserve_neighbors() {
    for count in [8, 1024, 1_000_000] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = external(931_000);
        let target = Pointer {
            block: "local:sparse-copy".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let destination = Pointer {
            block: "local:sparse-destination".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = CMemory::new()
            .with_block(target.block.clone(), count * 4)
            .with_block(destination.block.clone(), count * 4)
            .store(source.clone(), CValue::UInt32(11u32.into()))
            .store(
                source.offset_by_bytes((count - 1) * 4),
                CValue::UInt32(17u32.into()),
            );
        let middle = typed_load(&before, &source.offset_by_bytes(4));
        let memory = copy(before, &target, &source, count);
        let memory = copy(memory, &destination, &target, count);
        for (index, value) in [
            (0, CValue::UInt32(11u32.into())),
            (1, middle),
            (count - 1, CValue::UInt32(17u32.into())),
        ] {
            assert_eq!(
                typed_load(&memory, &destination.offset_by_bytes(index * 4)),
                value
            );
        }
        assert!(memory.cells.runs().count() <= 2);
        assert!(memory.cells.concrete().len() <= 6);
        let saved = typed_load(&memory, &destination.offset_by_bytes(4));
        let changed = memory.store(target.offset_by_bytes(4), CValue::UInt32(42u32.into()));
        assert_eq!(typed_load(&changed, &destination.offset_by_bytes(4)), saved);
    }
    let source = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = (0..5).fold(CMemory::new(), |memory, index| {
        memory.store(
            source.offset_by_bytes(index * 4),
            CValue::UInt32((index + 1).into()),
        )
    });
    let copied = copy(memory, &source.offset_by_bytes(4), &source, 3);
    for (index, value) in [(0, 1), (1, 1), (2, 2), (3, 3), (4, 5)] {
        assert_eq!(
            typed_load(&copied, &source.offset_by_bytes(index * 4)),
            CValue::UInt32(value.into())
        );
    }
}

#[test]
fn external_array_load_substitution_changes_only_the_copied_lane() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = external(932_000);
    let target = external(932_001);
    let memory = copy(CMemory::new(), &target, &source, 1_000_000);
    let CValue::UInt32(Bitvector32Term::Variable(variable)) =
        typed_load(&memory, &target.offset_by_bytes(4))
    else {
        panic!()
    };
    let previous = typed_load(&memory, &target);
    let following = typed_load(&memory, &target.offset_by_bytes(8));
    let (changed, work) = crate::instrumentation::measure_deterministic_work(|| {
        crate::kernel::reasoning::substitute_bitvector_variable_in_memory(
            &memory,
            variable,
            &23u32.into(),
        )
    });
    assert_eq!(
        typed_load(&changed, &target.offset_by_bytes(4)),
        CValue::UInt32(23u32.into())
    );
    assert_eq!(typed_load(&changed, &target), previous);
    assert_eq!(typed_load(&changed, &target.offset_by_bytes(8)), following);
    assert!(work < 10_000, "{work}");
    assert_eq!(changed.cells.concrete().len(), 1);
}

#[test]
fn external_array_snapshots_reject_invalid_storage_and_preserve_empty_semantics() {
    let source = external(934_000);
    let target = external(934_001);
    let context = PureFactContext::new();
    for (source, memory) in [
        (source.offset_by_bytes(1), CMemory::new()),
        (
            source.clone(),
            CMemory::new().store(source.clone(), CValue::Int32(1.into())),
        ),
        (
            Pointer {
                block: "local:uninitialized".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            CMemory::new().with_block("local:uninitialized", 16),
        ),
        (Pointer::null(), CMemory::new()),
    ] {
        assert!(
            memory
                .write_scalar_array_region(
                    &target,
                    CType::UInt32,
                    4,
                    CValue::pointer(source),
                    true,
                    false,
                    &context
                )
                .is_err()
        );
    }
    assert_eq!(copy(CMemory::new(), &target, &source, 0), CMemory::new());
    assert!(
        CMemory::new()
            .write_scalar_array_region(
                &target,
                CType::UInt32,
                0,
                CValue::UInt32(1u32.into()),
                true,
                false,
                &context
            )
            .is_err()
    );
}

#[test]
fn external_array_copy_representatives_cover_source_and_destination_stem_cancellation() {
    use crate::kernel::primitives::{CellRun, IndexIntervals, RunValueMode};
    let _session = crate::kernel::VerificationSession::enter();
    let source = external(938_000).offset_by_bytes(0);
    let destination = external(938_001);
    let shifted = |p: &Pointer, shift| Pointer {
        block: p.block.clone(),
        offset: PointerOffsetTerm::add(p.offset.clone(), PointerOffsetTerm::Constant(shift)),
    };
    for (source_shift, target_shift) in [(-4, -8), (-8, -4), (0, -4), (-4, 0)] {
        let source = shifted(&source, source_shift);
        let target = shifted(&destination, target_shift);
        let run = CellRun::new_with_mode(
            target,
            4,
            CType::UInt32,
            8,
            crate::kernel::intern_c_memory(CMemory::new()),
            RunValueMode::Copy {
                source_base: source,
            },
            IndexIntervals::default(),
        );
        let representatives = crate::kernel::reasoning::run_shape_representatives(&run).unwrap();
        assert!(representatives.contains(&0));
        for shift in [source_shift, target_shift] {
            if shift < 0 {
                assert!(representatives.contains(&((-shift / 4) as u32)));
            }
        }
        let memory = CMemory::new();
        let mut cells = (*memory.cells).clone();
        cells.add_run(run);
        assert_eq!(
            cells.map_cells(|p, v| (p.clone(), v.clone()), |_| None),
            cells
        );
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/tests/external_array_tests.rs");
}
