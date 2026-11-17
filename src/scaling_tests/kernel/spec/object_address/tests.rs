use super::*;

#[test]
fn typed_address_evaluation_does_not_walk_ambient_locals() {
    let mut samples = Vec::new();
    for count in [4, 32, 256] {
        let _session = VerificationSession::enter();
        let root = SymbolicMemory::global_pointer("addressed");
        let pointer = ProgramValue::typed_pointer(root, ProgramType::UInt8Pointer);
        let mut state = ExecutionState::new();
        for index in 0..count {
            state.locals.set(format!("unrelated_{index}"), int32(index));
        }
        let expression = address(SpecExpression::Value(pointer), false);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            evaluate_one(SpecScope::unbound(&state, None), &expression)
        });
        assert!(matches!(
            result.value.into_native(),
            ProgramValue::Pointer(_)
        ));
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}
