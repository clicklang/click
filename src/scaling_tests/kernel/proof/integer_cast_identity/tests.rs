// Scaling tests of `src/kernel/proof/integer_cast_identity.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn integer_cast_identity_promotes_only_canonical_unsigned_subword_carriers() {
    let word = Bitvector32Term::Variable(Variable(168_010));
    let observation = |ty, value| IntegerTerm::from_machine(ty, value).unwrap();
    let claim = |source, destination, carrier: Bitvector32Term| {
        let original = observation(source, carrier.clone());
        let goal = Proposition::ConditionIs(
            ConditionTerm::integer_equal(observation(destination, carrier), original.clone()),
            true,
        );
        let premises = vec![
            le(IntegerTerm::constant_i64(0), original.clone()),
            le(original, IntegerTerm::constant_i64(65535)),
        ];
        (premises, goal)
    };
    for source in [Ty::UInt8, Ty::UInt16] {
        let mask = (1u32 << source.format().bits()) - 1;
        for destination in [Ty::Int32, Ty::UInt32] {
            for reversed in [false, true] {
                let carrier = if reversed {
                    Bitvector32Term::bitwise_and(Bitvector32Term::Constant(mask), word.clone())
                } else {
                    Bitvector32Term::bitwise_and(word.clone(), Bitvector32Term::Constant(mask))
                };
                let (mut premises, goal) = claim(source, destination, carrier);
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
            }
            for carrier in [
                word.clone(),
                Bitvector32Term::bitwise_and(word.clone(), Bitvector32Term::Constant(mask + 1)),
            ] {
                let (premises, goal) = claim(source, destination, carrier);
                assert!(
                    certificate(goal.clone(), vec![0, 1])
                        .check(&goal, &premises)
                        .is_err()
                );
            }
        }
    }
    // A signed sub-word observation of 0xffff is negative, while a raw
    // word promotion of that mask is positive. Never admit that retagging.
    let (premises, goal) = claim(
        Ty::Int16,
        Ty::Int32,
        Bitvector32Term::bitwise_and(word, Bitvector32Term::Constant(65535)),
    );
    assert!(
        certificate(goal.clone(), vec![0, 1])
            .check(&goal, &premises)
            .is_err()
    );
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
