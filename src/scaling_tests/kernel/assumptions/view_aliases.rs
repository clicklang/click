#[test]
fn view_misses_do_not_enumerate_pointer_alias_classes() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer::symbolic(Variable(810_000));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context
                .equality_graph
                .add_equality(&base, &Pointer::symbolic(Variable(810_001 + index)));
        }
        let memory = CMemory::new();
        let goal = Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: 4096.into(),
            wide: false,
        };
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert!(!context.proves_atomic_without_search(&goal));
            }
        });
        samples.push(work);
    }
    eprintln!("alias-class view misses: {samples:?}");
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 16),
        "alias walk: {samples:?}"
    );
}
