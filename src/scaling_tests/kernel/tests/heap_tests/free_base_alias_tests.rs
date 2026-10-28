use super::*;

fn alias_free_work(selected: u32, unrelated: u32) -> usize {
    let _session = crate::kernel::VerificationSession::enter();
    let mut resources = ResourceContext::new();
    let mut facts = PureFactContext::new();
    let mut state = CState::new();
    for index in 0..selected + unrelated {
        let base = Pointer {
            block: PointerBlock::Heap(974_000 + u64::from(index)),
            offset: PointerOffsetTerm::Constant(0),
        };
        resources = resources.unchecked_with_fact(CResourceFact::own_allocation(base.clone(), 4));
        if index < selected {
            let alias = Pointer::symbolic(Variable(975_000 + u64::from(index)));
            facts = facts.assume_proposition(Proposition::ConditionIs(
                ConditionTerm::pointer_value_equal(
                    CPointerValue::new(alias.clone(), CType::Int32Pointer),
                    CPointerValue::new(base.clone(), CType::Int32Pointer),
                ),
                true,
            ));
            resources = resources.unchecked_with_fact(CResourceFact::own_memory(
                CMemoryRange::new(base, 0.into(), 1.into()),
            ));
            state = state.with_local(format!("q{index}"), CValue::pointer(alias));
        }
    }
    state = state.with_resource_context(resources);
    let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
        for index in 0..selected {
            let CStatementOutcome::Normal(after) = free_once(&state, &format!("q{index}"), &facts)
            else {
                panic!("alias free refused");
            };
            state = *after;
        }
    });
    assert_eq!(state.resources().facts().len(), unrelated as usize);
    work
}

#[test]
fn alias_free_ignores_unrelated_allocations_and_scales_with_steps() {
    let unrelated = [0, 16, 64, 256].map(|n| alias_free_work(4, n));
    assert!(
        unrelated.iter().all(|w| *w <= unrelated[0] + 64),
        "{unrelated:?}"
    );
    let steps = [8, 16, 32, 64].map(|n| alias_free_work(n, 64));
    assert!(steps[0] > 0);
    assert!(steps.windows(2).all(|p| p[1] <= 3 * p[0]), "{steps:?}");
}
