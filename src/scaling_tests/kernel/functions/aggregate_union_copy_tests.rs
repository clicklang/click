// Scaling tests of `src/kernel/functions.rs` (module `aggregate_union_copy_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

// A private argument copy must not manufacture read permission or turn
// an unwritten source object into an initialized parameter.
#[test]
fn aggregate_argument_reads_require_authority_and_initialization_and_scale() {
    for count in [4u32, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = Pointer {
            block: "aggregate-argument-source".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let layout = CAggregateLayout::new(
            count * 4,
            4,
            (0..count)
                .map(|i| CAggregateField::new(format!("field_{i}"), i * 4, CType::Int32))
                .collect(),
        );
        let parameters =
            [CParameter::new("input", CType::Int32Pointer).with_aggregate_layout(layout)];
        let values = [CValue::pointer(source.clone())];
        let assumptions = PureFactContext::new();
        let empty = CMemory::new().with_uninitialized_block(source.block.clone(), count * 4);
        let resources = ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
            CMemoryRange::new_with_element_width(source.clone(), 0.into(), (count * 4).into(), 1),
        ));
        let unwritten = CState::new()
            .with_memory(empty.clone())
            .with_resource_context(resources.clone());
        assert!(matches!(
            aggregate_argument_read_refusal(&unwritten, &parameters, &values, &assumptions),
            Some(CFunctionOutcome::UndefinedBehavior(
                CUndefinedBehavior::UninitializedRead
            ))
        ));
        let mut memory = empty;
        for i in 0..count {
            memory = memory.store(source.offset_by_bytes(i * 4), int32(i));
        }
        let unreadable = CState::new().with_memory(memory);
        assert!(matches!(
            aggregate_argument_read_refusal(&unreadable, &parameters, &values, &assumptions),
            Some(CFunctionOutcome::RuntimeError(
                CRuntimeError::MissingResource { .. }
            ))
        ));
        let readable = unreadable.with_resource_context(resources);
        // Warm the resource index outside the measurement. The measured
        // field walk must grow with the selected aggregate, not its square.
        assert!(
            aggregate_argument_read_refusal(&readable, &parameters, &values, &assumptions)
                .is_none()
        );
        let (refusal, work) = crate::instrumentation::measure_deterministic_work(|| {
            aggregate_argument_read_refusal(&readable, &parameters, &values, &assumptions)
        });
        assert!(refusal.is_none());
        assert!(
            work <= count as usize * 128 + 128,
            "{count} fields: {work} work"
        );
    }
}

#[test]
fn unsigned_aggregate_array_copies_preserve_values_and_scale() {
    let mut samples = Vec::new();
    for count in [4u32, 1024, 1_000_000] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = Pointer {
            block: "local:aggregate-array-source".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let destination = Pointer {
            block: "local:aggregate-array-target".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let layout = CAggregateLayout::new(
            count * 4,
            4,
            vec![CAggregateField::new("words", 0, CType::UInt32Array(count))],
        );
        let memory = CMemory::new()
            .with_block(source.block.clone(), count * 4)
            .with_block(destination.block.clone(), count * 4)
            .write_scalar_array_region(
                &source,
                CType::UInt32,
                count,
                CValue::UInt32(7u32.into()),
                false,
                false,
                &PureFactContext::new(),
            )
            .unwrap();
        let (copied, work) = crate::instrumentation::measure_deterministic_work(|| {
            copy_aggregate_fields_checked(memory, &source, &destination, &layout).unwrap()
        });
        let last = destination.offset_by_bytes((count - 1) * 4);
        assert_eq!(copied.known_value(&last), Some(CValue::UInt32(7u32.into())));
        let changed = copied.store(
            source.offset_by_bytes((count - 1) * 4),
            CValue::UInt32(9u32.into()),
        );
        assert_eq!(
            changed.known_value(&last),
            Some(CValue::UInt32(7u32.into()))
        );
        samples.push(work);
        // An unplaced store invalidates the compact source run and its
        // concrete last-lane override. The immutable copy is disjoint,
        // and every forgotten source byte remains initialized.
        let unplaced = source.offset_by_elements(Bitvector32Term::Variable(Variable(925_002)), 4);
        let (forgotten, work) = crate::instrumentation::measure_deterministic_work(|| {
            changed.without_possible_aliasing_cells(&unplaced, 4, &PureFactContext::new())
        });
        assert_eq!(forgotten.known_value(&source), None);
        assert_eq!(
            forgotten.known_value(&source.offset_by_bytes((count - 1) * 4)),
            None
        );
        assert!(forgotten.has_initialized_bytes_at(&source, count * 4));
        assert_eq!(
            forgotten.known_value(&last),
            Some(CValue::UInt32(7u32.into()))
        );
        samples.push(work);
        let (unknown, work) = crate::instrumentation::measure_deterministic_work(|| {
            copy_aggregate_fields_checked(forgotten, &source, &destination, &layout).unwrap()
        });
        assert!(unknown.known_value(&last).is_some());
        assert!(unknown.has_initialized_bytes_at(&destination, count * 4));
        samples.push(work);
        let uninitialized = CMemory::new()
            .with_block(source.block.clone(), count * 4)
            .with_block(destination.block.clone(), count * 4);
        assert_eq!(
            copy_aggregate_fields_checked(uninitialized, &source, &destination, &layout).err(),
            Some(CUndefinedBehavior::UninitializedRead)
        );
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] * 2 + 64),
        "{samples:?}"
    );
}
