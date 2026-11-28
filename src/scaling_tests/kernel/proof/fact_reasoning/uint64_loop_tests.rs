// Scaling tests of `src/kernel/proof/fact_reasoning.rs` (module `uint64_loop_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn uint64_successor_certificates_require_the_strict_guard_and_ignore_unrelated_facts() {
    let i = OldMachineTerm::Variable(Variable(980001));
    let n = OldMachineTerm::Variable(Variable(980002));
    let next = OldMachineTerm::uint64_add(i.clone(), OldMachineTerm::uint64_constant(1));
    let guard = Proposition::condition_is(
        OldConditionTerm::uint64_less_than(i.clone(), n.clone()),
        true,
    );
    let successor = Proposition::condition_is(
        OldConditionTerm::uint64_less_equal(next.clone(), n.clone()),
        true,
    );
    let descent = Proposition::condition_is(
        OldConditionTerm::uint64_less_than(
            OldMachineTerm::uint64_subtract(n.clone(), next),
            OldMachineTerm::uint64_subtract(n.clone(), i.clone()),
        ),
        true,
    );
    let mut samples = Vec::new();
    for size in [8, 32, 128] {
        let mut premises = vec![guard.clone()];
        premises.extend((0..size).map(|k| {
            Proposition::condition_is(
                OldConditionTerm::uint64_less_than(
                    OldMachineTerm::Variable(Variable(990000 + k)),
                    OldMachineTerm::uint64_constant(17),
                ),
                true,
            )
        }));
        let facts = crate::kernel::proof::PureFactStore::from_ordered(&premises);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            normalize_using_conditions(&successor, std::slice::from_ref(&guard), &facts)?;
            normalize_using_conditions(&descent, std::slice::from_ref(&guard), &facts)
        });
        result.unwrap();
        samples.push(work);
        // Ambient facts do not substitute for explicit certificate inputs.
        assert!(normalize_using_conditions(&successor, &[], &facts).is_err());
        assert!(normalize_using_conditions(&descent, &[], &facts).is_err());
    }
    assert!(samples[0] > 0);
    // Unrelated facts must not increase work; cheaper lookups are allowed.
    assert!(
        samples.iter().all(|work| *work <= samples[0]),
        "{samples:?}"
    );
    let weak = Proposition::condition_is(
        OldConditionTerm::uint64_less_equal(i.clone(), n.clone()),
        true,
    );
    let facts = crate::kernel::proof::PureFactStore::from_ordered(std::slice::from_ref(&weak));
    assert!(normalize_using_conditions(&successor, std::slice::from_ref(&weak), &facts).is_err());
    assert!(normalize_using_conditions(&descent, std::slice::from_ref(&weak), &facts).is_err());
    let missing = crate::kernel::proof::PureFactStore::from_ordered(&[]);
    assert!(matches!(
        normalize_using_conditions(&successor, &[guard], &missing),
        Err(ConditionalNormalizationError::UnavailablePremise(0))
    ));
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn uint64_truncation_certificates_require_full_width_bounds() {
    let i = OldMachineTerm::Variable(Variable(981011));
    let n = OldMachineTerm::Variable(Variable(981012));
    let low_i = OldMachineTerm::uint32_from_64(i.clone());
    let low_n = OldMachineTerm::uint32_from_64(n.clone());
    let guard = Proposition::condition_is(
        OldConditionTerm::uint64_less_than(i.clone(), n.clone()),
        true,
    );
    let bound = Proposition::condition_is(
        OldConditionTerm::uint64_less_equal(
            n.clone(),
            OldMachineTerm::uint64_constant(i32::MAX as u64),
        ),
        true,
    );
    let goal = Proposition::condition_is(
        OldConditionTerm::signed_less_than(low_i.clone(), low_n.clone()),
        true,
    );
    let mut samples = Vec::new();
    for size in [8, 32, 128, 512] {
        let mut available = vec![guard.clone(), bound.clone()];
        available.extend((0..size).map(|k| {
            Proposition::condition_is(
                OldConditionTerm::uint64_less_equal(
                    OldMachineTerm::Variable(Variable(982000 + k)),
                    OldMachineTerm::uint64_constant(1000),
                ),
                true,
            )
        }));
        let facts = crate::kernel::proof::PureFactStore::from_ordered(&available);
        let premises = [guard.clone(), bound.clone()];
        if samples.is_empty() {
            // Initialize the shared terms used by this certificate once.
            normalize_using_conditions(&goal, &premises, &facts).unwrap();
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            normalize_using_conditions(&goal, &premises, &facts)
        });
        result.unwrap();
        samples.push(work);
        assert!(normalize_using_conditions(&goal, &premises[..1], &facts).is_err());
        assert!(normalize_using_conditions(&goal, &premises[1..], &facts).is_err());
    }
    // The certificate must cost no more beside 64x as many unrelated facts.
    // Later samples can be cheaper as the shared term caches warm further.
    let baseline = samples[0];
    assert!(
        baseline > 0 && samples.iter().all(|work| *work <= baseline + 1),
        "{samples:?}"
    );
    let too_wide = Proposition::condition_is(
        OldConditionTerm::uint64_less_equal(n.clone(), OldMachineTerm::uint64_constant(1u64 << 32)),
        true,
    );
    let facts =
        crate::kernel::proof::PureFactStore::from_ordered(&[guard.clone(), too_wide.clone()]);
    assert!(normalize_using_conditions(&goal, &[guard, too_wide], &facts).is_err());

    let full_equal = Proposition::condition_is(OldConditionTerm::int64_equal(i.clone(), n), true);
    let low_equal = Proposition::condition_is(OldConditionTerm::equal(low_i.clone(), low_n), true);
    let facts =
        crate::kernel::proof::PureFactStore::from_ordered(std::slice::from_ref(&full_equal));
    normalize_using_conditions(&low_equal, &[full_equal], &facts).unwrap();
    let bound = Proposition::condition_is(
        OldConditionTerm::uint64_less_equal(i.clone(), OldMachineTerm::uint64_constant(1000)),
        true,
    );
    let facts = crate::kernel::proof::PureFactStore::from_ordered(std::slice::from_ref(&bound));
    for goal in [
        OldConditionTerm::signed_less_equal(OldMachineTerm::constant(0), low_i.clone()),
        OldConditionTerm::signed_less_equal(low_i, OldMachineTerm::constant(1000)),
    ] {
        // Lower-bound certificates need the explicit signed-range guard.
        let signed_bound = Proposition::condition_is(
            OldConditionTerm::uint64_less_equal(
                i.clone(),
                OldMachineTerm::uint64_constant(i32::MAX as u64),
            ),
            true,
        );
        normalize_using_conditions(&signed_bound, std::slice::from_ref(&bound), &facts).unwrap();
        let premises = [bound.clone(), signed_bound];
        let facts = crate::kernel::proof::PureFactStore::from_ordered(&premises);
        normalize_using_conditions(&Proposition::condition_is(goal, true), &premises, &facts)
            .unwrap();
    }
}

#[test]
fn retained_conditional_sums_normalize_from_selected_conditions() {
    use crate::kernel::machine_integer::comparison::retained_arithmetic_comparison;
    use crate::kernel::proof::PureFactStore;
    let selected_index = OldMachineTerm::Variable(Variable(994_001));
    let guard = Proposition::condition_is(
        OldConditionTerm::uint64_equal(selected_index.clone(), OldMachineTerm::uint64_constant(19)),
        true,
    );
    let high = 10_000_000_000_000_000_000u64;
    let mut costs = Vec::new();
    for size in [32, 64, 128] {
        let mut sum = OldMachineTerm::uint64_constant(0);
        for i in 0..size {
            let term = OldMachineTerm::if_then_else(
                OldConditionTerm::uint64_equal(
                    selected_index.clone(),
                    OldMachineTerm::uint64_constant(i),
                ),
                OldMachineTerm::uint64_constant(if i == 19 { high } else { 1 }),
                OldMachineTerm::uint64_constant(0),
            );
            sum = OldMachineTerm::uint64_add(sum, term);
        }
        let native = OldConditionTerm::uint64_equal(sum, OldMachineTerm::uint64_constant(high));
        let retained = retained_arithmetic_comparison(&native).unwrap();
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&guard));
        let goal = Proposition::condition_is(retained, true);
        let exports = KernelTermExport::machine_export_count();
        let (result, cost) = crate::instrumentation::measure_deterministic_work(|| {
            normalize_using_conditions(&goal, std::slice::from_ref(&guard), &facts)
        });
        result.unwrap();
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        normalize_using_conditions(
            &Proposition::condition_is(native, true),
            std::slice::from_ref(&guard),
            &facts,
        )
        .unwrap();
        assert!(normalize_using_conditions(&goal, &[], &facts).is_err());
        assert!(
            normalize_using_conditions(
                &goal,
                std::slice::from_ref(&guard),
                &PureFactStore::from_ordered(&[])
            )
            .is_err()
        );
        let wrong_guard = Proposition::condition_is(
            OldConditionTerm::uint64_equal(
                selected_index.clone(),
                OldMachineTerm::uint64_constant(18),
            ),
            true,
        );
        let wrong_facts = PureFactStore::from_ordered(std::slice::from_ref(&wrong_guard));
        assert!(normalize_using_conditions(&goal, &[wrong_guard], &wrong_facts).is_err());
        costs.push(cost);
    }
    assert!(costs[0] > 0);
    assert!(
        costs.windows(2).all(|pair| pair[1] <= pair[0] * 3 + 64),
        "{costs:?}"
    );
}
