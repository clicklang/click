use super::*;

#[test]
fn compound_read_query_ignores_cached_expression_size() {
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let slot = Address {
            base: "cached-expression".into(),
            offset: AddressOffset::Constant(0),
        };
        let mut cached = OldMachineTerm::Variable(Variable(989201));
        for _ in 0..size {
            cached = sum(M::Int32, cached, number(M::Int32, 1));
        }
        let memory =
            intern_memory(SymbolicMemory::new().store(slot.clone(), ProgramValue::Int32(cached)));
        crate::kernel::eval::record_load_access_width(memory.memory(), &slot, 4);
        let read =
            OldMachineTerm::read_named(ProgramPoint::at(&memory), Box::new(slot), LoadKind::Int32);
        let query = sum(M::Int32, read, number(M::Int32, 1));
        let graph = EqualityGraph::default();
        let (answer, work) = crate::instrumentation::measure_deterministic_work(|| {
            graph.are_int32_equal(&query, &number(M::Int32, 0))
        });
        assert!(!answer);
        samples.push(work);
    }
    // The first query can also initialize shared operator metadata. Growing
    // the cached expression must never increase the cold-query work.
    assert!(
        samples.iter().all(|work| *work <= samples[0]),
        "cold query must not substitute cached expressions: {samples:?}"
    );
}
