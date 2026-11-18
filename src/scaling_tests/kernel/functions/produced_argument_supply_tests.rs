// Scaling tests of primitive output preparation in kernel/functions.
use super::*;

fn check_returned_resource_construction(outputs: u32) {
    let mut samples = Vec::new();
    for count in [4_u64, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let entry = state(outputs);
        let pointer = Address {
            base: "produced-cells".into(),
            offset: AddressOffset::Constant(0),
        };
        let facts = (0..count).fold(PureFactContext::new(), |facts, index| {
            facts.assume_condition(
                ConditionTerm::address_equal(
                    pointer.clone(),
                    Address::symbolic(Variable(9_700_000 + index)),
                ),
                true,
            )
        });
        let function = program_function(ProgramType::Void, "outputs", vec![], program_skip())
            .with_resource_summary(vec![], (0..outputs).map(output).collect());
        let mut runs = Vec::new();
        for _ in 0..2 {
            let (returned, work) = crate::instrumentation::measure_deterministic_work(|| {
                evaluate_function_return_resource_context(
                    &function,
                    &[],
                    &entry,
                    &entry,
                    outputs as usize,
                    &facts,
                    &mut ExecutionBudget::beside_live_state(),
                )
                .unwrap()
                .unwrap()
            });
            assert_eq!(returned.facts().len(), outputs as usize);
            let (remaining, consumer_work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    let whole = ResourceFact::own_memory(MemoryRange::new(
                        pointer.clone(),
                        0u32.into(),
                        outputs.into(),
                    ));
                    returned
                        .clone()
                        .without_fact_incrementally(&whole, &facts)
                        .expect("the declared pieces supply the requested footprint")
                });
            assert!(remaining.facts().is_empty());
            assert_eq!(returned.facts().len(), outputs as usize);
            assert!(entry.resources().facts().is_empty());
            runs.push((work, consumer_work));
        }
        samples.push(runs);
    }
    eprintln!("{outputs} returned clauses, aliases 4/16/64/256: {samples:?}");
    for runs in &samples {
        for (work, baseline) in runs.iter().zip(&samples[0]) {
            assert!(
                work.0 <= baseline.0 + 16 && work.1 <= baseline.1 + 16,
                "{outputs}: {samples:?}"
            );
        }
    }
}

#[test]
fn one_returned_clause_ignores_pointer_aliases() {
    check_returned_resource_construction(1);
}

#[test]
fn adjacent_returned_clauses_ignore_pointer_aliases() {
    check_returned_resource_construction(2);
}

#[test]
#[ignore = "nightly: eight returned clauses and cold consumption at four alias sizes"]
fn eight_returned_clauses_ignore_pointer_aliases() {
    check_returned_resource_construction(8);
}

#[test]
fn produced_read_supply_scales_with_outputs_and_ignores_the_caller_frame() {
    let mut samples = Vec::new();
    for count in [4, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let function = program_function(ProgramType::Void, "outputs", vec![], program_skip())
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
        let function = program_function(ProgramType::Void, "outputs", vec![], program_skip())
            .with_resource_summary(vec![], vec![output(0)]);
        let mut entry = state(1);
        let mut bindings = BTreeMap::new();
        for index in 0..count {
            entry = entry.with_local(format!("unrelated_{index}"), int32(index));
            entry.resources = entry
                .resources
                .clone()
                .unchecked_with_fact(ResourceFact::own_token(
                    "unrelated".into(),
                    vec![int32(index)],
                ));
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
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "{samples:?}"
    );
}
