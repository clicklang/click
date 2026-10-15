// Scaling tests of `src/surface/checking/signed_arithmetic_planner.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn compound_premise_and_goal_evidence_scales_with_expression_size() {
    let mut work = Vec::new();
    for depth in [2usize, 4, 8, 16] {
        let mut a = var(1);
        let mut b = var(2);
        for _ in 0..depth {
            a = Bitvector32Term::Add(Box::new(a), Box::new(constant(0)));
            b = Bitvector32Term::Add(Box::new(b), Box::new(constant(0)));
        }
        let premises = [
            le(
                Bitvector32Term::add(a.clone(), b.clone()),
                Bitvector32Term::add(constant(1000), b),
            ),
            le(constant(0), var(1)),
            le(var(1), constant(2000)),
            le(constant(1), var(2)),
            le(var(2), constant(1000)),
        ];
        let goal = le(Bitvector32Term::add(a, constant(1)), constant(1001));
        let (plan, measured) =
            crate::instrumentation::measure_deterministic_work(|| check_plan(&goal, &premises));
        assert!(plan.nodes.len() <= 20 * depth + 64);
        work.push(measured);
    }
    assert!(work.windows(2).all(|pair| pair[1] > pair[0]), "{work:?}");
    assert!(
        work.windows(2).all(|pair| pair[1] <= 3 * pair[0] + 128),
        "{work:?}"
    );
}

#[test]
fn checked_affine_premise_evidence_scales_with_both_expression_roots() {
    let mut work = Vec::new();
    for depth in [2usize, 4, 8, 16] {
        let mut a = var(1);
        let mut b = var(2);
        for _ in 0..depth {
            a = Bitvector32Term::Add(Box::new(a), Box::new(constant(0)));
            b = Bitvector32Term::Add(Box::new(b), Box::new(constant(0)));
        }
        let sum = Bitvector32Term::Add(Box::new(a), Box::new(b.clone()));
        let difference = Bitvector32Term::Add(Box::new(constant(1000)), Box::new(b));
        let premises = [
            le(sum, difference),
            le(constant(0), var(1)),
            le(var(1), constant(2000)),
            le(constant(1), var(2)),
            le(var(2), constant(1000)),
        ];
        let (plan, measured) = crate::instrumentation::measure_deterministic_work(|| {
            check_plan(&le(var(1), constant(1000)), &premises)
        });
        assert!(plan.nodes.iter().any(|node| matches!(node, SignedArithmeticNode::AffinePremise { left_evidence, right_evidence, .. } if left_evidence != right_evidence)));
        assert!(plan.nodes.len() <= 12 * depth + 32);
        work.push(measured);
    }
    assert!(work.windows(2).all(|pair| pair[1] > pair[0]), "{work:?}");
    assert!(
        work.windows(2).all(|pair| pair[1] <= 3 * pair[0] + 128),
        "{work:?}"
    );
}

#[test]
fn two_sided_compound_affine_evidence_scales_with_shared_depth() {
    let mut work = Vec::new();
    for depth in [2usize, 4, 8, 16] {
        let mut left_base = var(1);
        let mut right_base = var(2);
        for _ in 0..depth {
            left_base = Bitvector32Term::Add(Box::new(left_base), Box::new(constant(0)));
            right_base = Bitvector32Term::Add(Box::new(right_base), Box::new(constant(0)));
        }
        let left = Bitvector32Term::Add(Box::new(left_base), Box::new(constant(1)));
        let right = Bitvector32Term::Add(Box::new(right_base), Box::new(constant(1)));
        let goal = le(left, right);
        let premises = vec![
            le(var(1), var(2)),
            le(constant(0), var(1)),
            le(var(1), constant(100)),
            le(constant(0), var(2)),
            le(var(2), constant(100)),
        ];
        let (plan, measured) = crate::instrumentation::measure_deterministic_work(|| {
            let plan = check_plan(&goal, &premises);
            assert!(plan.nodes.iter().any(|node| matches!(
                node,
                SignedArithmeticNode::AffineConclusionWithEvidence { .. }
            )));
            plan
        });
        assert!(!plan.nodes.is_empty());
        work.push(measured);
    }
    assert!(work.windows(2).all(|pair| pair[1] > pair[0]), "{work:?}");
    assert!(
        work.windows(2).all(|pair| pair[1] <= 4 * pair[0] + 64),
        "two-sided evidence should have bounded scaling: {work:?}"
    );
}

#[test]
fn scale_factor_work_charges_large_coefficients_and_key_lookups() {
    let atom = SignedArithmeticAtom::from_term(&var(31)).unwrap();
    let source = SignedArithmeticClaim {
        carrier: SignedArithmeticCarrier::SignedInt32,
        relation: SignedArithmeticRelation::LessEqual,
        terms: BTreeMap::from([(atom.clone(), BigInt::one())]),
        constant: BigInt::zero(),
    };
    let mut measurements = Vec::new();
    for bits in [8usize, 16, 32, 64] {
        let target = SignedArithmeticClaim {
            carrier: SignedArithmeticCarrier::SignedInt32,
            relation: SignedArithmeticRelation::LessEqual,
            terms: BTreeMap::from([(atom.clone(), BigInt::one() << bits)]),
            constant: BigInt::zero(),
        };
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| scale_factor(&source, &target));
        assert_eq!(result, Some(BigInt::one() << bits));
        measurements.push(work);
    }
    assert!(
        measurements.windows(2).all(|pair| pair[1] > pair[0]),
        "scale-factor BigInt work must scale: {measurements:?}"
    );
    assert!(
        measurements
            .windows(2)
            .all(|pair| pair[1] <= 8 * pair[0] + 64),
        "scale-factor work should have bounded scaling: {measurements:?}"
    );
}
