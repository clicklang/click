#[test]
fn aggregate_step_results_cost_their_fields_instead_of_unrelated_state() {
    for unrelated in [false, true] {
        let mut work_by_size = Vec::new();
        for size in [1, 16, 256] {
            let _session = VerificationSession::enter();
            let fields = if unrelated { 1 } else { size };
            let (mut state, source, layout) = fixture(fields);
            if unrelated {
                for i in 0..size {
                    let pointer = Memory::local_pointer(format!("other{i}"));
                    state.set_memory(
                        state
                            .memory
                            .clone()
                            .with_block(pointer.block.clone(), 4)
                            .store(pointer, int32(i)),
                    );
                }
            }
            let mut budget = ExecutionBudget::for_new_execution();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let result = materialize(&state, &source, &layout, &mut budget);
                end_aggregate_step_lifetimes(&result, &[0]).unwrap();
            });
            work_by_size.push((size as usize, work));
        }
        if unrelated {
            assert!(
                work_by_size
                    .iter()
                    .all(|(_, work)| *work <= work_by_size[0].1 + 64),
                "{work_by_size:?}"
            );
        } else {
            let base = work_by_size[0].1;
            assert!(
                work_by_size
                    .iter()
                    .all(|(size, work)| *work <= base * size * 2),
                "{work_by_size:?}"
            );
        }
    }
}
