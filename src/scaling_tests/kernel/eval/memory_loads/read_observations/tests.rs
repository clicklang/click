use super::*;

#[test]
fn unobserved_read_inspection_is_indexed_and_leaves_no_record() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let memory = intern_c_memory(Memory::new());
        let pointer = Pointer::symbolic(Variable(998_708));
        for i in 1..=size {
            record(
                &memory,
                &pointer.offset_by_bytes(i * 4),
                LoadKind::Int32,
                &memory,
                4,
            );
        }
        let read =
            MachineTerm::MemoryLoad(memory.clone(), Box::new(pointer.clone()), LoadKind::Int32);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                for_operand(MachineOperandView::Legacy(&read))
                    .unwrap()
                    .bytes,
                8
            );
        });
        assert!(existing(&memory, &pointer, LoadKind::Int32).is_none());
        samples.push(work);
    }
    assert!(samples[0] > 0);
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn selected_read_metadata_stays_indexed_as_observations_and_branches_grow() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let memory = intern_c_memory(Memory::new());
        let address = Pointer::symbolic(Variable(998_703));
        let term = KernelTerm::scalar_read_descriptor(
            MachineIntegerType::Int32,
            &memory,
            &address,
            LoadKind::Int32,
        )
        .unwrap();
        let id = record(&memory, &address, LoadKind::Int32, &memory, 4);
        remember_term(&term, id);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for i in 0..size {
                record(
                    &memory,
                    &address.offset_by_bytes(i * 8 + 8),
                    LoadKind::Int32,
                    &memory,
                    4,
                );
                let parent = capture();
                record(&memory, &address, LoadKind::Int32, &memory, 8);
                assert_eq!(
                    for_operand(MachineOperandView::Shared(&term))
                        .unwrap()
                        .bytes,
                    8
                );
                restore(&parent);
                assert_eq!(
                    for_operand(MachineOperandView::Shared(&term))
                        .unwrap()
                        .bytes,
                    4
                );
            }
        });
        assert_eq!(load_variable_registry_len(), 0);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{samples:?}");
    }
}

#[test]
fn cyclic_frame_observations_scale_with_distinct_selected_reads() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let mut facts = Vec::new();
        let mut bounds = Vec::new();
        for index in 0..size {
            let (fact, bound) = cyclic_frame_read(index);
            facts.push(fact);
            bounds.push(bound);
        }
        let proposition = facts
            .into_iter()
            .reduce(|left, right| Proposition::And(Box::new(left), Box::new(right)))
            .unwrap();
        let (variables, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut variables = std::collections::BTreeSet::new();
            crate::kernel::reasoning::variable_collection::collect_proposition_frame_variables(
                &proposition,
                &mut variables,
            );
            variables
        });
        assert!(bounds.iter().all(|bound| variables.contains(bound)));
        samples.push(work);
    }
    assert!(samples[0] > 0);
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{samples:?}");
    }
}
