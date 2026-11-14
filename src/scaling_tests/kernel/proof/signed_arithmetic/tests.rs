// Scaling tests of `src/kernel/proof/signed_arithmetic.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::{MachineCastSpelling, MachineTerm};

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
                    .atom(MachineTerm::Variable(Variable(1000 + index as u64)))
                    .unwrap();
                let right_atom = arena
                    .atom(MachineTerm::Variable(Variable(1000 + index as u64)))
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
                    .atom(MachineTerm::Variable(Variable(2000 + index as u64)))
                    .unwrap();
                let right_atom = arena
                    .atom(MachineTerm::Variable(Variable(2000 + index as u64)))
                    .unwrap();
                left_shared = arena.binary(CheckedBinaryOperator::Add, left_shared, left_atom);
                right_shared = arena.binary(CheckedBinaryOperator::Add, right_shared, right_atom);
            }
            for index in 0..size {
                let left_atom = arena
                    .atom(MachineTerm::Variable(Variable(3000 + index as u64)))
                    .unwrap();
                let right_atom = arena
                    .atom(MachineTerm::Variable(Variable(3000 + index as u64)))
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
                MachineTerm::legacy_cast(
                    MachineCastSpelling::UInt32From64,
                    Box::new(MachineTerm::Variable(Variable(index as u64))),
                )
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
        let term = MachineTerm::PureFunctionApplication {
            name: "opaque".repeat(payload_size),
            arguments: (0..payload_size)
                .map(|index| MachineTerm::Variable(Variable(index as u64)))
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
        term = MachineTerm::PureFunctionApplication {
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
        term = MachineTerm::PureFunctionApplication {
            name: "f".to_string(),
            arguments: vec![term],
        };
    }
    let premise = le(term, MachineTerm::constant(1));
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
    let goal = le(x(), MachineTerm::constant(1));
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
            term = MachineTerm::PureFunctionApplication {
                name: "f".to_string(),
                arguments: vec![term],
            };
        }
        let premise = le(term, MachineTerm::constant(1));
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
        term = MachineTerm::PureFunctionApplication {
            name: "f".to_string(),
            arguments: vec![term],
        };
    }
    let goal = le(term.clone(), MachineTerm::constant(0));
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
                term: MachineTerm::constant(0),
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
    let premise = le(MachineTerm::constant(0), MachineTerm::constant(0));
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
            let mut atom = MachineTerm::Variable(Variable(index as u64));
            for depth in 0..size {
                atom = MachineTerm::PureFunctionApplication {
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

#[test]
fn mathematical_certificate_result_decoding_scales_with_explicit_atoms() {
    use crate::kernel::IntegerTerm;

    let mut measurements = Vec::new();
    for size in [4usize, 8, 16, 32] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut terms = (0..size)
            .map(|index| {
                IntegerTerm::from_machine(
                    MachineIntegerType::Int32,
                    MachineTerm::Variable(Variable(991_920 + index as u64)),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        while terms.len() > 1 {
            terms = terms
                .as_chunks::<2>()
                .0
                .iter()
                .map(|pair| IntegerTerm::add(pair[0].clone(), pair[1].clone()))
                .collect();
        }
        let proposition = Proposition::ConditionIs(
            ConditionTerm::integer_less_equal(terms.pop().unwrap(), IntegerTerm::constant_i64(0)),
            true,
        );
        let (claim, work) = crate::instrumentation::measure_deterministic_work(|| {
            signed_arithmetic_integer_result(&proposition).unwrap()
        });
        assert_eq!(claim.terms.len(), size);
        measurements.push(work);
    }
    assert!(measurements[0] > 0);
    for pair in measurements.windows(2) {
        assert!(
            pair[1] > pair[0],
            "decoder work must be charged: {measurements:?}"
        );
        assert!(
            pair[1] <= pair[0] * 3 + 64,
            "explicit affine decoder work must scale near linearly: {measurements:?}"
        );
    }
}

#[test]
fn exact_definedness_refuses_small_mismatch_without_expanding_shared_guard() {
    use crate::kernel::{IntegerTerm, KernelTerm, KernelType, SharedMachineIntegerTerm};
    let format = MachineIntegerType::Int32;
    let mut measurements = Vec::new();
    for size in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut root = KernelTerm::variable(KernelType::C(format.c_type()), Variable(982300));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::arithmetic_binary(
                    format,
                    MachineBinaryOp::Add,
                    [root.clone(), root.clone()],
                )
                .unwrap();
                let observation =
                    SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap();
                let exact = IntegerTerm::add(
                    IntegerTerm::Machine(observation.clone()),
                    IntegerTerm::constant_i64(1),
                );
                let guard = Proposition::And(
                    Box::new(Proposition::ConditionIs(
                        ConditionTerm::integer_less_equal(
                            exact.clone(),
                            IntegerTerm::constant_i64(i32::MAX as i64),
                        ),
                        true,
                    )),
                    Box::new(Proposition::ConditionIs(
                        ConditionTerm::integer_greater_equal(
                            exact,
                            IntegerTerm::constant_i64(i32::MIN as i64),
                        ),
                        true,
                    )),
                );
                let small = MachineTerm::Binary {
                    format,
                    op: MachineBinaryOp::Add,
                    left: Box::new(x()),
                    right: Box::new(MachineTerm::constant(1)),
                };
                assert!(!is_exact_definedness(&guard, &small));
                assert!(!observation.has_boxed_operand());
            }
        });
        measurements.push((size, work));
    }
    for pair in measurements.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small * 4 <= sw * large * 5, "{measurements:?}");
    }
}

#[test]
fn definedness_source_matching_reuses_shared_prefixes() {
    use crate::kernel::{
        IntegerTerm, KernelTerm, KernelTermImport, KernelType, SharedMachineIntegerTerm,
    };
    let mut samples = Vec::new();
    for size in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut import = KernelTermImport::default();
        let mut left = import.machine(format, &MachineTerm::constant(1));
        let mut right = import.machine(format, &MachineTerm::uint32_constant(1));
        let variable = KernelTerm::variable(
            KernelType::C(crate::kernel::ProgramType::Int32),
            Variable(982500),
        );
        left = KernelTerm::machine_binary_shared(
            format,
            MachineBinaryOp::Add,
            [left, variable.clone()],
        );
        right = KernelTerm::machine_binary_shared(format, MachineBinaryOp::Add, [right, variable]);
        let guard = |operand: SharedMachineIntegerTerm| {
            let exact = IntegerTerm::Add(
                IntegerTerm::Machine(operand).into(),
                IntegerTerm::constant(1.into()).into(),
            );
            Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::integer_less_equal(
                        exact.clone(),
                        IntegerTerm::constant(i32::MAX.into()),
                    ),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::integer_greater_equal(
                        exact,
                        IntegerTerm::constant(i32::MIN.into()),
                    ),
                    true,
                )),
            )
        };
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                left = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [left.clone(), left.clone()],
                );
                right = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [right.clone(), right.clone()],
                );
                let a = SharedMachineIntegerTerm::from_shared(format, left.clone()).unwrap();
                let b = SharedMachineIntegerTerm::from_shared(format, right.clone()).unwrap();
                let (ga, gb) = (guard(a.clone()), guard(b.clone()));
                assert!(signed_arithmetic_source_matches(&ga, &gb));
                assert!(signed_arithmetic_source_matches(&gb, &ga));
                assert!(!signed_arithmetic_source_matches(
                    &ga,
                    &Proposition::ConditionIs(ConditionTerm::Constant(false), false)
                ));
                assert!(!a.has_boxed_operand());
                assert!(!b.has_boxed_operand());
            }
        });
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small * 4 <= sw * large * 5, "{samples:?}");
    }
}
