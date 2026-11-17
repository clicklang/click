use super::*;

#[test]
fn function_pointer_read_query_does_not_scan_aliases_or_cells() {
    for related in [false, true] {
        let mut samples = Vec::new();
        for size in [16u64, 64, 256, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let cell = |i| Pointer {
                block: "callbacks".into(),
                offset: PointerOffsetTerm::Constant(i * 8),
            };
            let mut memory = Memory::new();
            let mut facts = PureFactContext::new();
            for i in 1..=size {
                memory = memory.store(cell(i as i64), callback_value("other"));
                facts = facts.assume_condition(
                    ConditionTerm::pointer_equal(
                        Pointer::symbolic(Variable(993000 + i)),
                        if related { cell(0) } else { cell(i as i64) },
                    ),
                    true,
                );
            }
            let value = callback_value("callback");
            memory = memory.store(cell(0), value);
            let memory = intern_memory(memory);
            let query = Pointer::symbolic(Variable(999000));
            facts =
                facts.assume_condition(ConditionTerm::pointer_equal(query.clone(), cell(0)), true);
            // Measure a cold miss: no producer equation has been admitted.
            let read = function_read(&memory, &query);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.pointers_known_equal(&read, &Pointer::function("absent"))
            });
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|p| p[0] == p[1]),
            "related={related}: {samples:?}"
        );
    }
}
