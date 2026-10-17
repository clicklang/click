// Scaling tests of `src/kernel/proof/fact_reasoning.rs` (module `uint64_loop_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn uint64_successor_certificates_require_the_strict_guard_and_ignore_unrelated_facts() {
    let i = Bitvector32Term::Variable(Variable(980001));
    let n = Bitvector32Term::Variable(Variable(980002));
    let next = Bitvector32Term::uint64_add(i.clone(), Bitvector32Term::UInt64Constant(1));
    let guard =
        Proposition::ConditionIs(ConditionTerm::uint64_less_than(i.clone(), n.clone()), true);
    let successor = Proposition::ConditionIs(
        ConditionTerm::uint64_less_equal(next.clone(), n.clone()),
        true,
    );
    let descent = Proposition::ConditionIs(
        ConditionTerm::uint64_less_than(
            Bitvector32Term::uint64_subtract(n.clone(), next),
            Bitvector32Term::uint64_subtract(n.clone(), i.clone()),
        ),
        true,
    );
    let mut samples = Vec::new();
    for size in [8, 32, 128] {
        let mut premises = vec![guard.clone()];
        premises.extend((0..size).map(|k| {
            Proposition::ConditionIs(
                ConditionTerm::uint64_less_than(
                    Bitvector32Term::Variable(Variable(990000 + k)),
                    Bitvector32Term::UInt64Constant(17),
                ),
                true,
            )
        }));
        let facts = crate::kernel::proof::ProofFacts::from_ordered(&premises);
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
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
    let weak =
        Proposition::ConditionIs(ConditionTerm::uint64_less_equal(i.clone(), n.clone()), true);
    let facts = crate::kernel::proof::ProofFacts::from_ordered(std::slice::from_ref(&weak));
    assert!(normalize_using_conditions(&successor, std::slice::from_ref(&weak), &facts).is_err());
    assert!(normalize_using_conditions(&descent, std::slice::from_ref(&weak), &facts).is_err());
    let missing = crate::kernel::proof::ProofFacts::from_ordered(&[]);
    assert!(matches!(
        normalize_using_conditions(&successor, &[guard], &missing),
        Err(ConditionalNormalizationError::UnavailablePremise(0))
    ));
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn uint64_truncation_certificates_require_full_width_bounds() {
    let i = Bitvector32Term::Variable(Variable(981011));
    let n = Bitvector32Term::Variable(Variable(981012));
    let low_i = Bitvector32Term::uint32_from_64(i.clone());
    let low_n = Bitvector32Term::uint32_from_64(n.clone());
    let guard =
        Proposition::ConditionIs(ConditionTerm::uint64_less_than(i.clone(), n.clone()), true);
    let bound = Proposition::ConditionIs(
        ConditionTerm::uint64_less_equal(
            n.clone(),
            Bitvector32Term::UInt64Constant(i32::MAX as u64),
        ),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(low_i.clone(), low_n.clone()),
        true,
    );
    let mut samples = Vec::new();
    for size in [8, 32, 128, 512] {
        let mut available = vec![guard.clone(), bound.clone()];
        available.extend((0..size).map(|k| {
            Proposition::ConditionIs(
                ConditionTerm::uint64_less_equal(
                    Bitvector32Term::Variable(Variable(982000 + k)),
                    Bitvector32Term::UInt64Constant(1000),
                ),
                true,
            )
        }));
        let facts = crate::kernel::proof::ProofFacts::from_ordered(&available);
        let premises = [guard.clone(), bound.clone()];
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            normalize_using_conditions(&goal, &premises, &facts)
        });
        result.unwrap();
        samples.push(work);
        assert!(normalize_using_conditions(&goal, &premises[..1], &facts).is_err());
        assert!(normalize_using_conditions(&goal, &premises[1..], &facts).is_err());
    }
    assert!(
        samples[0] > 0 && samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
    let too_wide = Proposition::ConditionIs(
        ConditionTerm::uint64_less_equal(n.clone(), Bitvector32Term::UInt64Constant(1u64 << 32)),
        true,
    );
    let facts = crate::kernel::proof::ProofFacts::from_ordered(&[guard.clone(), too_wide.clone()]);
    assert!(normalize_using_conditions(&goal, &[guard, too_wide], &facts).is_err());

    let full_equal = Proposition::ConditionIs(ConditionTerm::int64_equal(i.clone(), n), true);
    let low_equal = Proposition::ConditionIs(ConditionTerm::equal(low_i.clone(), low_n), true);
    let facts = crate::kernel::proof::ProofFacts::from_ordered(std::slice::from_ref(&full_equal));
    normalize_using_conditions(&low_equal, &[full_equal], &facts).unwrap();
    let bound = Proposition::ConditionIs(
        ConditionTerm::uint64_less_equal(i.clone(), Bitvector32Term::UInt64Constant(1000)),
        true,
    );
    let facts = crate::kernel::proof::ProofFacts::from_ordered(std::slice::from_ref(&bound));
    for goal in [
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), low_i.clone()),
        ConditionTerm::signed_less_equal(low_i, Bitvector32Term::Constant(1000)),
    ] {
        // Lower-bound certificates need the explicit signed-range guard.
        let signed_bound = Proposition::ConditionIs(
            ConditionTerm::uint64_less_equal(
                i.clone(),
                Bitvector32Term::UInt64Constant(i32::MAX as u64),
            ),
            true,
        );
        normalize_using_conditions(&signed_bound, std::slice::from_ref(&bound), &facts).unwrap();
        let premises = [bound.clone(), signed_bound];
        let facts = crate::kernel::proof::ProofFacts::from_ordered(&premises);
        normalize_using_conditions(&Proposition::ConditionIs(goal, true), &premises, &facts)
            .unwrap();
    }
}
