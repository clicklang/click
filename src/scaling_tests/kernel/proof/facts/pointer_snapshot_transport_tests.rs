use super::*;
#[test]
fn full_pointer_fact_transport_checks_designations_and_the_whole_read() {
    let _session = VerificationSession::enter();
    let cell = Pointer {
        block: "pointer-snapshot-cell".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = intern_c_memory(CMemory::new().with_block(cell.block.clone(), 8));
    let after = intern_c_memory(before.memory().clone().with_block("other-local", 4));
    let pointer = |memory: &SharedCMemory| {
        CPointerValue::from_read(
            Pointer::loaded_value(memory, &cell),
            CType::Int32Pointer,
            memory,
            &cell,
        )
    };
    let rhs = CPointerValue::new(Pointer::symbolic(Variable(991_100)), CType::Int32Pointer);
    let fact = |pointer| {
        Proposition::ConditionIs(
            ConditionTerm::PointerValueEqual(Box::new(pointer), Box::new(rhs.clone())),
            true,
        )
    };
    let source = fact(pointer(&before));
    let target = fact(pointer(&after));
    let origin = Arc::new(Pointer::symbolic(Variable(991_101)));
    let forged = fact(
        pointer(&after)
            .with_designation(origin.clone())
            .with_opaque_extent(Some(origin)),
    );
    let overwritten = intern_c_memory(
        after
            .memory()
            .clone()
            .store(cell.clone().offset_by_bytes(4), CValue::UInt32(0u32.into())),
    );
    let wrong_snapshot = fact(pointer(&overwritten));
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut facts = ProofFacts::from_ordered(std::slice::from_ref(&source));
        for index in 0..size {
            facts = facts.with_fact(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(992_100 + index)),
                    Bitvector32Term::Constant(7),
                ),
                true,
            ));
        }
        for index in 0..size {
            let selected = pointer(&before).with_extent(Some(SubobjectExtent {
                start: cell.clone(),
                width: index + 1,
            }));
            facts = facts.with_fact(Proposition::ConditionIs(
                ConditionTerm::PointerValueEqual(Box::new(selected.clone()), Box::new(selected)),
                true,
            ));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(facts.matching_fact_across_effects(&target, &[]).is_some());
            assert!(facts.matching_fact_across_effects(&forged, &[]).is_none());
            assert!(
                facts
                    .matching_fact_across_effects(&wrong_snapshot, &[])
                    .is_none()
            );
        });
        samples.push(work);
    }
    assert!(samples[3] <= samples[0] * 4 + 64, "{samples:?}");
}
