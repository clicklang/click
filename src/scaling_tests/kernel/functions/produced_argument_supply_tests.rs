// Scaling tests of primitive output preparation in kernel/functions.
use super::*;

#[test]
fn produced_read_supply_scales_with_outputs_and_ignores_the_caller_frame() {
    let mut samples = Vec::new();
    for count in [4, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let function = c_function(CType::Void, "outputs", vec![], c_skip())
            .with_resource_summary(vec![], (0..count).map(output).collect());
        let entry = state(count);
        let mut evaluation = entry.clone();
        let (prepared, work) = crate::instrumentation::measure_deterministic_work(|| {
            prepare_produced_argument_supply(
                &entry,
                &mut evaluation,
                function.contract_interface(),
                &PureFactContext::new(),
                &mut ExecutionBudget::beside_live_state(),
            )
            .unwrap()
        });
        assert_eq!(prepared.len(), count as usize);
        assert!(prepared.iter().all(Option::is_some));
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 6, "{samples:?}");
    }
    let mut samples = Vec::new();
    for count in [0, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let function = c_function(CType::Void, "outputs", vec![], c_skip())
            .with_resource_summary(vec![], vec![output(0)]);
        let mut entry = state(1);
        let mut bindings = BTreeMap::new();
        for index in 0..count {
            entry = entry.with_local(format!("unrelated_{index}"), int32(index));
            entry.resources = entry.resources.clone().unchecked_with_fact(
                CResourceFact::own_token("unrelated".into(), vec![int32(index)]),
            );
            // Consumed instances can retain their logical binding without
            // current custody. No primitive output depends on these names.
            let identity = Variable(910_000 + u64::from(index));
            bindings.insert(identity, identity);
        }
        entry.resource_bindings = Some(Arc::new(bindings));
        let mut evaluation = entry.clone();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            prepare_produced_argument_supply(
                &entry,
                &mut evaluation,
                function.contract_interface(),
                &PureFactContext::new(),
                &mut ExecutionBudget::beside_live_state(),
            )
            .unwrap()
        });
        samples.push(work);
    }
    assert!(samples.windows(2).all(|pair| pair[0] == pair[1]), "{samples:?}");
}
