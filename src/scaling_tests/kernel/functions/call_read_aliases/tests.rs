// Scaling tests of the selected typed-read bridge at a checked call.
use super::*;

#[test]
fn selected_call_read_alias_work_ignores_unrelated_cells_and_facts() {
    let mut samples = Vec::new();
    for size in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut f = fixture();
        // A generic symbolic address may alias any of these stores. Use a
        // distinct local object so their history is truly unrelated.
        f.address = CMemory::frame_local_pointer(30, "selected");
        for i in 0..size {
            let at = CMemory::frame_local_pointer(30, &format!("ambient{i}"));
            f.before = f.before.clone().with_memory(
                f.before
                    .memory()
                    .clone()
                    .store(at.clone(), CValue::Int32((i as u32).into())),
            );
            f.assumptions = f.assumptions.assume_proposition(Proposition::Predicate {
                name: format!("ambient{i}"),
                arguments: vec![],
            });
        }
        f.rewritten = CallReadState::new(&f.before, &f.aliases);
        // Snapshot creation and its existing substitution are outside the
        // selected-read measurement. Warm interning, as the call's producer does.
        intern_c_memory_ref(f.before.memory());
        intern_c_memory_ref(f.rewritten.memory());
        // The first selected source read pays the scalar normalizer's cold
        // epoch work. Compare another fresh cell in the same history so the
        // bridge may not add history-dependent work of its own.
        let (_, baseline) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::canonical_form_of_load(
                intern_c_memory_ref(f.before.memory()),
                CMemory::frame_local_pointer(30, "baseline"),
                LoadKind::Bits64,
            )
        });
        let _scope = CallReadAliasScope::enter([&f.rewritten]);
        let bridge = || {
            let (_, facts) = observe(&f.rewritten, &f.address, CType::UInt64, &f.assumptions);
            let mut caller = PureFactContext::new();
            for fact in facts {
                caller = caller.assume_execution_pure_fact(&fact);
            }
            caller
        };
        let (_, cold) = crate::instrumentation::measure_deterministic_work(bridge);
        let (_, warm) = crate::instrumentation::measure_deterministic_work(bridge);
        samples.push((cold.saturating_sub(baseline), warm));
    }
    assert!(
        samples
            .iter()
            .all(|(extra, warm)| *extra <= samples[0].0 + 64 && *warm <= samples[0].1 + 64),
        "{samples:?}"
    );
}
