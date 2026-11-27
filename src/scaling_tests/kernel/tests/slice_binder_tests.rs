// Scaling tests of `src/kernel/tests/slice_binder_tests.rs`: deterministic
// work measured at several input sizes. Included into its `scaling_tests`
// module; see "Scaling tests" in `docs/internals/testing.md`.

use super::*;

/// `body` beside `size` conjuncts about unrelated slices: `t.len() == i` and
/// `t == u` for each.
fn with_unrelated_slices(body: Proposition, size: u64, base: u64) -> Proposition {
    (0..size).fold(body, |proposition, index| {
        let (t, u) = (Variable(base + 2 * index), Variable(base + 2 * index + 1));
        Proposition::And(
            Box::new(proposition),
            Box::new(Proposition::And(
                Box::new(Proposition::condition_is(
                    OldConditionTerm::uint64_equal(
                        count_of(t),
                        OldMachineTerm::uint64_constant(index),
                    ),
                    true,
                )),
                Box::new(Proposition::condition_is(
                    OldConditionTerm::pointer_equal(named(t), named(u)),
                    true,
                )),
            )),
        )
    })
}

/// Closing over a slice binder and opening it again walk the body once each,
/// its count beside it: the work grows linearly as unrelated slices, with
/// their own counts, join the body.
#[test]
fn closing_a_slice_binder_grows_linearly_with_unrelated_slices() {
    let costs = [8u64, 32, 128].map(|size| {
        let _session = VerificationSession::enter();
        let (binder, other) = (Variable(967_000), Variable(967_001));
        let body = with_unrelated_slices(body_over(&named(binder), other), size, 968_000);
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            let closed =
                close_forall(BinderName::default(), binder, slice_sort(), &body).expect("closes");
            let (var, closed_body) = quantifier_parts(&closed);
            let (witness, opened) =
                open_quantifier(var, &slice_sort(), closed_body).expect("opens");
            assert!(proposition_variables(&opened).contains(&witness.element_count()));
        });
        work
    });
    for pair in costs.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{costs:?}");
    }
}

/// Instantiating one slice quantifier reads its own body and the value: the
/// work is the same however many unrelated slice quantifiers exist.
#[test]
fn instantiating_a_slice_binder_ignores_unrelated_binders() {
    let costs = [8u64, 32, 128].map(|size| {
        let _session = VerificationSession::enter();
        let unrelated = (0..size)
            .map(|index| forall_over(Variable(969_000 + 2 * index), Variable(969_001 + 2 * index)))
            .collect::<Vec<_>>();
        let closed = forall_over(Variable(967_100), Variable(967_101));
        let (var, body) = quantifier_parts(&closed);
        let value = named(Variable(967_102));
        let (instantiated, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::substitute_pointer_value_in_proposition(body, *var, &value).unwrap()
        });
        assert_eq!(instantiated, body_over(&value, Variable(967_101)));
        assert_eq!(unrelated.len() as u64, size);
        work
    });
    assert!(
        costs.windows(2).all(|pair| pair[0] == pair[1]),
        "instantiating a slice binder grew with unrelated binders: {costs:?}"
    );
}
