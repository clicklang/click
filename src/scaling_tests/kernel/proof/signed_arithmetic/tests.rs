// Scaling tests of `src/kernel/proof/signed_arithmetic.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn repeated_deep_term_equivalence_has_linear_work_scaling() {
    let mut measurements = Vec::new();
    for depth in [8usize, 16, 32, 64] {
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut arena = TermArena::default();
            let mut left = arena.atom(x()).unwrap();
            let mut right = arena.atom(x()).unwrap();
            for index in 0..depth {
                let left_atom = arena
                    .atom(Bitvector32Term::Variable(Variable(1000 + index as u64)))
                    .unwrap();
                let right_atom = arena
                    .atom(Bitvector32Term::Variable(Variable(1000 + index as u64)))
                    .unwrap();
                left = arena.binary(CheckedBinaryOperator::Add, left, left_atom);
                right = arena.binary(CheckedBinaryOperator::Add, right, right_atom);
            }
            for _ in 0..depth {
                assert!(arena.equivalent(left, right));
            }
        });
        measurements.push(work);
    }
    for pair in measurements.windows(2) {
        assert!(
            pair[1] <= 3 * pair[0] + 8,
            "memoized deep equivalence should scale linearly: {measurements:?}"
        );
    }
}

#[test]
fn shared_subgraph_equivalence_is_cached_across_distinct_roots() {
    let mut measurements = Vec::new();
    for size in [8usize, 16, 32, 64] {
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut arena = TermArena::default();
            let mut left_shared = arena.atom(x()).unwrap();
            let mut right_shared = arena.atom(x()).unwrap();
            for index in 0..size {
                let left_atom = arena
                    .atom(Bitvector32Term::Variable(Variable(2000 + index as u64)))
                    .unwrap();
                let right_atom = arena
                    .atom(Bitvector32Term::Variable(Variable(2000 + index as u64)))
                    .unwrap();
                left_shared = arena.binary(CheckedBinaryOperator::Add, left_shared, left_atom);
                right_shared = arena.binary(CheckedBinaryOperator::Add, right_shared, right_atom);
            }
            for index in 0..size {
                let left_atom = arena
                    .atom(Bitvector32Term::Variable(Variable(3000 + index as u64)))
                    .unwrap();
                let right_atom = arena
                    .atom(Bitvector32Term::Variable(Variable(3000 + index as u64)))
                    .unwrap();
                let left_root = arena.binary(CheckedBinaryOperator::Add, left_shared, left_atom);
                let right_root = arena.binary(CheckedBinaryOperator::Add, right_shared, right_atom);
                assert!(arena.equivalent(left_root, right_root));
            }
        });
        measurements.push(work);
    }
    for pair in measurements.windows(2) {
        assert!(
            pair[1] <= 4 * pair[0] + 16,
            "shared subgraph comparison should not retraverse roots: {measurements:?}"
        );
    }
}

#[test]
fn narrowed_variable_atom_identity_work_scales_linearly() {
    let mut previous = None;
    for size in [16usize, 64, 256, 1024] {
        let terms: Vec<_> = (0..size)
            .map(|index| {
                Bitvector32Term::UInt32From64(Box::new(Bitvector32Term::Variable(Variable(
                    index as u64,
                ))))
            })
            .collect();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for term in &terms {
                assert_eq!(SignedArithmeticAtom::from_term(term).unwrap().work(), 1);
            }
        });
        assert!(work > 0);
        if let Some(previous) = previous {
            assert!(work <= 4 * previous + 4);
        }
        previous = Some(work);
    }
}

#[test]
fn opaque_payload_work_scales_with_application_identity() {
    let mut measurements = Vec::new();
    for payload_size in [8usize, 16, 32, 64] {
        let term = Bitvector32Term::PureFunctionApplication {
            name: "opaque".repeat(payload_size),
            arguments: (0..payload_size)
                .map(|index| Bitvector32Term::Variable(Variable(index as u64)))
                .collect(),
        };
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(!crate::instrumentation::deadline_exceeded_with_work(
                signed_term_work(&term,)
            ));
        });
        measurements.push(work);
    }
    for pair in measurements.windows(2) {
        assert!(
            pair[1] > pair[0],
            "opaque payloads must be charged by their full identity: {measurements:?}"
        );
        assert!(pair[1] <= 5 * pair[0], "{measurements:?}");
    }
}

#[test]
fn deep_opaque_payload_work_is_iterative_and_budgeted() {
    let mut term = x();
    for _ in 0..4096 {
        term = Bitvector32Term::PureFunctionApplication {
            name: "f".to_string(),
            arguments: vec![term],
        };
    }
    assert!(is_opaque_atom(&term));
    let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
        assert!(!crate::instrumentation::deadline_exceeded_with_work(
            signed_term_work(&term)
        ));
    });
    assert!(work > 4096);
}

#[test]
fn deep_opaque_payload_certificate_check_is_iterative() {
    let mut term = x();
    for _ in 0..4096 {
        term = Bitvector32Term::PureFunctionApplication {
            name: "f".to_string(),
            arguments: vec![term],
        };
    }
    let premise = le(term, Bitvector32Term::Constant(1));
    let certificate = SignedArithmeticCertificate {
        nodes: vec![SignedArithmeticNode::Premise {
            index: 0,
            result: claim(&premise),
        }],
        conclusion: 0,
    };
    let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
        certificate.check(&premise, std::slice::from_ref(&premise))
    });
    assert_eq!(result, Ok(()));
    assert!(work > 4096);
}

#[test]
fn certificate_check_work_scales_with_node_count() {
    let goal = le(x(), Bitvector32Term::Constant(1));
    let premise = std::slice::from_ref(&goal);
    let mut measurements = Vec::new();
    for count in [8usize, 16, 32, 64, 128] {
        let certificate = SignedArithmeticCertificate {
            nodes: (0..count)
                .map(|_| SignedArithmeticNode::Premise {
                    index: 0,
                    result: claim(&goal),
                })
                .collect(),
            conclusion: count - 1,
        };
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            certificate.check(&goal, premise)
        });
        assert_eq!(result, Ok(()));
        measurements.push(work);
    }
    assert!(
        measurements
            .windows(2)
            .all(|pair| pair[1] <= 3 * pair[0] + 64),
        "certificate checking should scale with supplied nodes: {measurements:?}"
    );
}

#[test]
fn deep_certificate_check_work_has_bounded_scaling() {
    let mut measurements = Vec::new();
    for depth in [128usize, 256, 512, 1024, 2048] {
        let mut term = x();
        for _ in 0..depth {
            term = Bitvector32Term::PureFunctionApplication {
                name: "f".to_string(),
                arguments: vec![term],
            };
        }
        let premise = le(term, Bitvector32Term::Constant(1));
        let certificate = SignedArithmeticCertificate {
            nodes: vec![SignedArithmeticNode::Premise {
                index: 0,
                result: claim(&premise),
            }],
            conclusion: 0,
        };
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            certificate.check(&premise, std::slice::from_ref(&premise))
        });
        assert_eq!(result, Ok(()));
        measurements.push(work);
    }
    assert!(
        measurements
            .windows(2)
            .all(|pair| pair[1] <= 3 * pair[0] + 128),
        "deep certificate checks should have bounded scaling: {measurements:?}"
    );
}

#[test]
fn deep_interval_proposition_conclusion_uses_bounded_identity() {
    let mut term = x();
    for _ in 0..1024 {
        term = Bitvector32Term::PureFunctionApplication {
            name: "f".to_string(),
            arguments: vec![term],
        };
    }
    let goal = le(term.clone(), Bitvector32Term::Constant(0));
    let premise_claim = claim(&goal);
    let certificate = SignedArithmeticCertificate {
        nodes: vec![
            SignedArithmeticNode::Premise {
                index: 0,
                result: premise_claim,
            },
            SignedArithmeticNode::IntervalFromAffine {
                source: 0,
                term: term.clone(),
                lower: SIGNED_MIN,
                upper: 0,
            },
            SignedArithmeticNode::IntervalAtom {
                carrier: SignedArithmeticCarrier::SignedInt32,
                term: Bitvector32Term::Constant(0),
                lower: 0,
                upper: 0,
            },
            SignedArithmeticNode::IntervalCompare {
                left: 1,
                right: 2,
                comparison: SignedArithmeticComparison::LessEqual,
                result: goal.clone(),
            },
        ],
        conclusion: 3,
    };
    let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
        certificate.check(&goal, std::slice::from_ref(&goal))
    });
    assert_eq!(result, Ok(()));
    assert!(work > 1024);
}

#[test]
fn scale_work_grows_with_coefficient_magnitude() {
    let premise = le(Bitvector32Term::Constant(0), Bitvector32Term::Constant(0));
    let mut measurements = Vec::new();
    for bits in [8usize, 16, 32, 64] {
        let coefficient = BigInt::one() << bits;
        let result = claim(&premise);
        let certificate = SignedArithmeticCertificate {
            nodes: vec![
                SignedArithmeticNode::Premise {
                    index: 0,
                    result: claim(&premise),
                },
                SignedArithmeticNode::Scale {
                    source: 0,
                    coefficient,
                    result,
                },
            ],
            conclusion: 1,
        };
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            certificate.check(&premise, std::slice::from_ref(&premise))
        });
        assert_eq!(checked, Ok(()));
        measurements.push(work);
    }
    assert!(measurements.windows(2).all(|pair| pair[1] > pair[0]));
    assert!(
        measurements
            .windows(2)
            .all(|pair| pair[1] <= 8 * pair[0] + 64),
        "coefficient work should have bounded scaling: {measurements:?}"
    );
}

#[test]
fn affine_multi_key_and_deep_atom_work_scales() {
    let mut measurements = Vec::new();
    for size in [4usize, 8, 16, 32] {
        let mut terms = BTreeMap::new();
        for index in 0..size {
            let mut atom = Bitvector32Term::Variable(Variable(index as u64));
            for depth in 0..size {
                atom = Bitvector32Term::PureFunctionApplication {
                    name: format!("f{depth}"),
                    arguments: vec![atom],
                };
            }
            let key = SignedArithmeticAtom::from_term(&atom).unwrap();
            terms.insert(key, BigInt::one());
        }
        let claim = SignedArithmeticClaim {
            carrier: SignedArithmeticCarrier::SignedInt32,
            relation: SignedArithmeticRelation::LessEqual,
            terms,
            constant: BigInt::zero(),
        };
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(same_int32_claim(&claim, &claim));
        });
        measurements.push(work);
    }
    assert!(
        measurements.windows(2).all(|pair| pair[1] > pair[0]),
        "multi-key deep atom work must scale: {measurements:?}"
    );
}
