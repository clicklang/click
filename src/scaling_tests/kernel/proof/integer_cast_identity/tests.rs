// Scaling tests of `src/kernel/proof/integer_cast_identity.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// A narrow value's 32-bit widening is identified with the value in work
/// independent of the ambient premises, when the certificate cites bounds on
/// the value inside its own format; bounds past that format, a premise that
/// is not a bound, and a 32-bit word that is not the value's widening are
/// refused.
#[test]
fn integer_cast_identity_identifies_only_the_widening_of_a_narrow_value() {
    let word = Bitvector32Term::Variable(Variable(168_010));
    let observation = |ty, value| IntegerTerm::from_machine(ty, value).unwrap();
    let equal =
        |left, right| Proposition::ConditionIs(ConditionTerm::integer_equal(left, right), true);
    for source in [Ty::UInt8, Ty::UInt16, Ty::Int8, Ty::Int16] {
        let narrow = Bitvector32Term::machine_integer_cast(Ty::Int32, source, word.clone());
        let original = observation(source, narrow.clone());
        let bounds = |lo: num_bigint::BigInt, hi: num_bigint::BigInt| {
            vec![
                le(IntegerTerm::constant(lo), original.clone()),
                le(original.clone(), IntegerTerm::constant(hi)),
            ]
        };
        let (lo, hi) = source.format().bounds();
        let mask = (1u32 << source.format().bits()) - 1;
        for destination in [Ty::Int32, Ty::UInt32] {
            if !destination.format().contains(source.format()) {
                continue;
            }
            let widened =
                Bitvector32Term::machine_integer_cast(source, destination, narrow.clone());
            let goal = equal(observation(destination, widened), original.clone());
            let mut premises = bounds(lo.clone(), hi.clone());
            let mut costs = Vec::new();
            for ambient in [0, 16, 64, 256, 1024] {
                premises.resize_with(ambient + 2, || {
                    Proposition::ConditionIs(ConditionTerm::Variable(Variable(168_011)), true)
                });
                let cert = certificate(goal.clone(), vec![0, 1]);
                let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                    cert.check(&goal, &premises)
                });
                result.unwrap();
                costs.push(work);
                assert!(
                    certificate(goal.clone(), vec![0, 2])
                        .check(&goal, &premises)
                        .is_err()
                );
            }
            assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
            for (lower, upper) in [(lo.clone() - 1, hi.clone()), (lo.clone(), hi.clone() + 1)] {
                assert!(
                    certificate(goal.clone(), vec![0, 1])
                        .check(&goal, &bounds(lower, upper))
                        .is_err(),
                    "{source:?} -> {destination:?}"
                );
            }
            // A bare word, a mask of it by anything but the format's mask,
            // or a word built by 32-bit arithmetic is no widening of the
            // value, whatever bounds are cited.
            for carrier in [
                word.clone(),
                Bitvector32Term::bitwise_and(word.clone(), Bitvector32Term::Constant(mask)),
                Bitvector32Term::bitwise_and(word.clone(), Bitvector32Term::Constant(mask + 1)),
                Bitvector32Term::add(word.clone(), Bitvector32Term::Constant(1)),
                Bitvector32Term::add(
                    Bitvector32Term::bitwise_and(word.clone(), Bitvector32Term::Constant(mask)),
                    Bitvector32Term::Constant(1),
                ),
            ] {
                let goal = equal(observation(destination, carrier), original.clone());
                assert!(
                    certificate(goal.clone(), vec![0, 1])
                        .check(&goal, &bounds(lo.clone(), hi.clone()))
                        .is_err(),
                    "{source:?} -> {destination:?}"
                );
            }
        }
    }
}

#[test]
fn legacy_integer_cast_identity_work_depends_on_nodes_and_explicit_bounds() {
    let value = Bitvector32Term::Variable(Variable(168_001));
    let original = IntegerTerm::from_machine(Ty::Int64, value.clone()).unwrap();
    let observed =
        IntegerTerm::from_machine(Ty::UInt64, Bitvector32Term::UInt64FromInt64(value.into()))
            .unwrap();
    let goal = Proposition::ConditionIs(
        ConditionTerm::integer_equal(observed, original.clone()),
        true,
    );
    let mut premises = vec![
        le(IntegerTerm::constant_i64(0), original.clone()),
        le(original, IntegerTerm::constant_i64(i64::MAX)),
    ];
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        premises.resize_with(size, || {
            Proposition::ConditionIs(ConditionTerm::Variable(Variable(168_003)), true)
        });
        let cert = certificate(goal.clone(), vec![0, 1]);
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| cert.check(&goal, &premises));
        result.unwrap();
        samples.push(work);
    }
    assert!(
        samples.iter().max().unwrap() - samples.iter().min().unwrap() <= 32,
        "{samples:?}"
    );
    let mut previous = None;
    for size in [2usize, 8, 32, 128] {
        let cert = SpecialArithmeticCertificate {
            nodes: vec![
                SpecialArithmeticNode::IntegerCastIdentity {
                    bounds: vec![0, 1],
                    result: goal.clone()
                };
                size
            ],
            conclusion: size - 1,
        };
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| cert.check(&goal, &premises));
        result.unwrap();
        assert!(work <= 4096 * size, "{size}: {work}");
        if let Some(before) = previous {
            assert!(work <= 4 * before + 64);
        }
        previous = Some(work);
    }
}

#[test]
fn integer_cast_identity_checks_only_explicit_premises_and_scales_with_nodes() {
    let (mut premises, goal) = inputs(Ty::Int128, Ty::Int64);
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        premises.resize_with(size, || {
            Proposition::ConditionIs(ConditionTerm::Variable(Variable(168_003)), true)
        });
        let cert = certificate(goal.clone(), vec![0, 1]);
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| cert.check(&goal, &premises));
        result.unwrap();
        samples.push(work);
    }
    assert!(
        samples.iter().max().unwrap() - samples.iter().min().unwrap() <= 32,
        "{samples:?}"
    );
    let mut previous = None;
    for size in [2usize, 8, 32, 128] {
        let cert = SpecialArithmeticCertificate {
            nodes: vec![
                SpecialArithmeticNode::IntegerCastIdentity {
                    bounds: vec![0, 1],
                    result: goal.clone()
                };
                size
            ],
            conclusion: size - 1,
        };
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| cert.check(&goal, &premises));
        result.unwrap();
        assert!(work <= 4096 * size, "{size}: {work}");
        if let Some(before) = previous {
            assert!(work <= 4 * before + 64);
        }
        previous = Some(work);
    }
}
