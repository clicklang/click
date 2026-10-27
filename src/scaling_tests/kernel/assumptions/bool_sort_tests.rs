// Scaling tests of `src/kernel/assumptions/bool_sort_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// Work at each size grows no faster than the size: the measurement at
/// double the size is at most a little over double.
fn grows_linearly(work: &[usize]) -> bool {
    work.windows(2)
        .all(|pair| pair[1] <= pair[0] * 2 + pair[0] / 2 + 64)
}

/// A nested `Bool` body, `c_k = if p_k { c_(k-1) } else { false }` over a
/// binder `c_0`, is decided by opening one conditional per level on demand
/// (rule L-If): each part is decided once, so the work is linear in the
/// depth, and assuming the facts does not open anything.
#[test]
fn a_nested_bool_conditional_is_decided_in_work_linear_in_its_depth() {
    let mut assume_work = Vec::new();
    let mut decide_work = Vec::new();
    for size in [4u64, 8, 16, 32] {
        let _session = VerificationSession::enter();
        let mut body = binder(500_000);
        for level in 0..size {
            body = bool_if(
                positive(501_000 + level),
                body,
                ConditionTerm::Constant(false),
            );
        }
        let (context, assumed) = crate::instrumentation::measure_deterministic_work(|| {
            let mut context = PureFactContext::new().assume_condition(binder(500_000), true);
            for level in 0..size {
                context = context.assume_condition(positive(501_000 + level), true);
            }
            context
        });
        let (value, decided) =
            crate::instrumentation::measure_deterministic_work(|| context.decide(&body));
        assert_eq!(value, Some(true), "size={size}");
        assume_work.push(assumed);
        decide_work.push(decided);
    }
    assert!(grows_linearly(&assume_work), "assume work {assume_work:?}");
    assert!(grows_linearly(&decide_work), "decide work {decide_work:?}");
}

/// A chain of `size` true equalities `v_0 == v_1`, ..., each a merge of two
/// classes (rule L-Eq), with one function's unfolding equation at every
/// link: filing them is linear in the chain, and once `v_0` is known every
/// member's truth is one class lookup, whatever the chain's length.
#[test]
fn bool_equality_merges_cost_constant_work_per_link() {
    let mut assume_work = Vec::new();
    let mut decide_work = Vec::new();
    for size in [4u64, 8, 16, 32] {
        let _session = VerificationSession::enter();
        let (context, assumed) = crate::instrumentation::measure_deterministic_work(|| {
            let mut context = PureFactContext::new();
            for link in 0..size {
                context = context.assume_condition(
                    bool_equal(binder(510_000 + link), binder(510_000 + link + 1)),
                    true,
                );
                let ConditionTerm::BoolApplication(application) = applied("level", 511_000 + link)
                else {
                    unreachable!("an application")
                };
                context = context.assume_proposition(ConditionTerm::bool_unfold_equation(
                    application,
                    binder(510_000 + link),
                ));
            }
            context.assume_condition(binder(510_000), true)
        });
        let last = applied("level", 511_000 + size - 1);
        let (value, decided) =
            crate::instrumentation::measure_deterministic_work(|| context.decide(&last));
        assert_eq!(value, Some(true), "size={size}");
        assume_work.push(assumed);
        decide_work.push(decided);
    }
    assert!(grows_linearly(&assume_work), "assume work {assume_work:?}");
    let first = decide_work[0];
    assert!(
        decide_work
            .iter()
            .all(|work| *work <= first + first / 2 + 64),
        "decision work grew with the chain: {decide_work:?}"
    );
}
