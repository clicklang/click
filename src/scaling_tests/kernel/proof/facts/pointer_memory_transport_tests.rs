use super::*;
#[test]
fn full_pointer_fact_transport_checks_provenance_and_the_whole_read() {
    let _session = VerificationSession::enter();
    let cell = Address {
        base: "pointer-retained_state-cell".into(),
        offset: AddressOffset::Constant(0),
    };
    let before = intern_memory(SymbolicMemory::new().with_block(cell.base.clone(), 8));
    let after = intern_memory(before.memory().clone().with_block("other-local", 4));
    let pointer = |memory: &SharedMemory| {
        Pointer::from_read(
            Address::loaded_value(memory, &cell),
            ProgramType::Int32Pointer,
            memory,
            &cell,
        )
    };
    let rhs = Pointer::new(
        Address::symbolic(Variable(991_100)),
        ProgramType::Int32Pointer,
    );
    let fact = |pointer| {
        Proposition::ConditionIs(
            ConditionTerm::PointerEqual(Box::new(pointer), Box::new(rhs.clone())),
            true,
        )
    };
    let source = fact(pointer(&before));
    let target = fact(pointer(&after));
    let origin = Arc::new(Address::symbolic(Variable(991_101)));
    let forged = fact(
        pointer(&after)
            .with_provenance(origin.clone())
            .with_bounds_owner(Some(origin)),
    );
    let overwritten = intern_memory(after.memory().clone().store(
        cell.clone().offset_by_bytes(4),
        ProgramValue::UInt32(0u32.into()),
    ));
    let wrong_state = fact(pointer(&overwritten));
    let mut samples = Vec::new();
    for size in [4u64, 16, 64, 256] {
        let mut facts = PureFactStore::from_ordered(std::slice::from_ref(&source));
        for index in 0..size {
            facts = facts.with_fact(Proposition::ConditionIs(
                ConditionTerm::equal(
                    MachineTerm::Variable(Variable(992_100 + index)),
                    MachineTerm::constant(7),
                ),
                true,
            ));
        }
        for index in 0..size {
            let selected = pointer(&before).with_bounds(Some(SubobjectBounds {
                start: cell.clone(),
                width: MachineTerm::constant(u32::try_from(index + 1).unwrap()),
            }));
            facts = facts.with_fact(Proposition::ConditionIs(
                ConditionTerm::PointerEqual(Box::new(selected.clone()), Box::new(selected)),
                true,
            ));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(facts.matching_fact_across_effects(&target, &[]).is_some());
            assert!(facts.matching_fact_across_effects(&forged, &[]).is_none());
            assert!(
                facts
                    .matching_fact_across_effects(&wrong_state, &[])
                    .is_none()
            );
        });
        samples.push(work);
    }
    eprintln!("full-pointer transport work: {samples:?}");
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "{samples:?}"
    );
}
