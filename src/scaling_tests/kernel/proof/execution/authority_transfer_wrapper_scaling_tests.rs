// Scaling tests of `src/kernel/proof/execution.rs` (module `authority_transfer_wrapper_scaling_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn ordinary_authority_wrapper_checks_only_its_delta() {
    // An ordinary wrapper around an authorized member reaches population
    // accounting and must authenticate its exchange. A wrapper around a
    // plain token instead keeps the ordinary definition law: its recorded
    // successor comes from the fold/unfold producer, not arbitrary test input.
    let member_definition =
        CCompositeResourceDefinition::new("member", vec![], None, false, vec![], vec![])
            .with_authorized(true);
    let definition = CCompositeResourceDefinition::new(
        "held",
        vec![],
        None,
        false,
        vec![CResourceSpec::composite(
            CResourceAccessMode::Own,
            "member".into(),
            vec![],
            vec![],
        )],
        vec![],
    );
    let function = c_function(
        CType::Void,
        "wrapper_scaling",
        vec![],
        CStatement::Return(CExpression::Value(CValue::Void)),
    )
    .with_composite_resource_definitions(vec![definition, member_definition]);
    let wrapper = function
        .proof_composite_resource_definition("held")
        .unwrap();
    assert!(!wrapper.is_authorized());
    assert!(wrapper.reaches_population());
    let selected = CResourceFact::own_composite("held".into(), vec![]);
    let child = CResourceFact::own_composite("member".into(), vec![]);
    let samples = [64usize, 256, 1024].map(|size| {
        let mut before = CState::new().with_population_creation_tracking();
        let mut facts = ProofFacts::default();
        let mut memory = CMemory::new();
        let mut resources = ResourceContext::new().unchecked_with_fact(child.clone());
        for index in 0..size {
            let unrelated = CResourceFact::own_token(format!("other_{index}"), vec![]);
            resources = resources.unchecked_with_fact(unrelated);
            before = before.with_local(format!("local_{index}"), int32(index as u32));
            memory = memory.with_block(format!("block_{index}"), 4);
            resources =
                resources.unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                    Pointer {
                        block: format!("block_{index}").into(),
                        offset: crate::kernel::PointerOffsetTerm::Constant(0),
                    },
                    0.into(),
                    1.into(),
                )));
            facts = facts.with_fact(Proposition::ConditionIs(
                crate::kernel::ConditionTerm::Bitvector32Equal(
                    Box::new(Bitvector32Term::Variable(Variable(index as u64 + 100))),
                    Box::new(Bitvector32Term::Constant(index as u32)),
                ),
                true,
            ));
        }
        before = before.with_memory(memory).with_resource_context(resources);
        let folded_resources = before
            .resources()
            .clone()
            .without_fact_incrementally(&child, facts.assumptions())
            .unwrap()
            .try_compose_with_facts_delaying_normalization(
                std::iter::once(selected.clone()),
                facts.assumptions(),
            )
            .unwrap();
        let folded = before.clone().with_resource_context(folded_resources);
        let unfolded_resources = folded
            .resources()
            .clone()
            .without_fact_incrementally(&selected, facts.assumptions())
            .unwrap()
            .try_compose_with_facts_delaying_normalization(
                std::iter::once(child.clone()),
                facts.assumptions(),
            )
            .unwrap();
        let unfolded = folded.clone().with_resource_context(unfolded_resources);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for (input, output) in [(&before, &folded), (&folded, &unfolded)] {
                CheckedResourceRewrite::check(
                    &function,
                    input,
                    &facts,
                    &selected,
                    output,
                    &facts,
                    &CheckedCallEvents::default(),
                )
                .expect("one wrapper rewrite preserves its unrelated frame");
            }
        });
        let unrelated = CResourceFact::own_token("other_0".into(), vec![]);
        let forged = folded.clone().with_resource_context(
            folded
                .resources()
                .clone()
                .without_fact_incrementally(&unrelated, facts.assumptions())
                .unwrap(),
        );
        assert!(
            CheckedResourceRewrite::check(
                &function,
                &before,
                &facts,
                &selected,
                &forged,
                &facts,
                &CheckedCallEvents::default(),
            )
            .is_err(),
            "the unrelated frame must remain authenticated"
        );
        let unrelated_memory = CResourceFact::own_memory(CMemoryRange::new(
            Pointer {
                block: "block_0".into(),
                offset: crate::kernel::PointerOffsetTerm::Constant(0),
            },
            0.into(),
            1.into(),
        ));
        for (input, output) in [(&before, &folded), (&folded, &unfolded)] {
            let forged = output.clone().with_resource_context(
                output
                    .resources()
                    .clone()
                    .without_fact_incrementally(&unrelated_memory, facts.assumptions())
                    .unwrap(),
            );
            assert!(
                CheckedResourceRewrite::check(
                    &function,
                    input,
                    &facts,
                    &selected,
                    &forged,
                    &facts,
                    &CheckedCallEvents::default(),
                )
                .is_err(),
                "a wrapper exchange cannot remove unrelated memory"
            );
        }
        work
    });
    assert!(
        samples[0] > 0,
        "the measured checker must charge work: {samples:?}"
    );
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 128),
        "wrapper work must grow at most logarithmically with its unrelated frame: {samples:?}"
    );
}
