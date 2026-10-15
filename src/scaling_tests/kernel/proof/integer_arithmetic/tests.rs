// Scaling tests of `src/kernel/proof/integer_arithmetic.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn nonlinear_integer_atoms_do_not_traverse_their_operand_dags() {
    let mut shared_work = Vec::new();
    for size in [8usize, 16, 32, 64] {
        let mut child = IntegerTerm::var(Variable(93001));
        for _ in 0..size {
            child = IntegerTerm::add(child.clone(), child.clone());
        }
        let divisor = IntegerTerm::var(Variable(93002));
        for atom in [
            IntegerTerm::multiply(child.clone(), divisor.clone()),
            IntegerTerm::truncating_quotient(child.clone(), divisor.clone()),
            IntegerTerm::truncating_remainder(child.clone(), divisor.clone()),
        ] {
            let atom: crate::kernel::SharedIntegerTerm = atom.into();
            let id = atom.id();
            let goal = proposition(ConditionTerm::IntegerLessEqual(
                atom,
                IntegerTerm::constant_i64(0).into(),
            ));
            let (result, work) =
                crate::instrumentation::measure_deterministic_work(|| claim(&goal));
            assert_eq!(
                result.terms,
                BTreeMap::from([(IntegerAffineAtom::Nonlinear(id), BigInt::one())])
            );
            shared_work.push(work);
        }
    }
    assert!(
        shared_work.iter().all(|work| *work == shared_work[0]),
        "{shared_work:?}"
    );
}

#[test]
fn opaque_integer_atoms_scale_with_affine_wrappers_and_distinct_atoms() {
    let mut samples = Vec::new();
    for size in [8usize, 16, 32, 64] {
        let divisor = IntegerTerm::var(Variable(94001));
        let mut expression = IntegerTerm::constant_i64(0);
        for index in 0..size {
            let atom = IntegerTerm::multiply(
                IntegerTerm::var(Variable(95000 + index as u64)),
                divisor.clone(),
            );
            expression = IntegerTerm::add(expression, atom);
        }
        let goal = proposition(ConditionTerm::integer_less_equal(
            expression,
            IntegerTerm::constant_i64(0),
        ));
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| claim(&goal));
        assert_eq!(result.terms.len(), size);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 3, "{samples:?}");
    }
}

#[test]
fn integer_affine_dag_scaling_includes_distinct_variables_and_shared_paths() {
    let mut distinct_work = Vec::new();
    let mut shared_work = Vec::new();
    for size in [8usize, 16, 32, 64] {
        let mut distinct = IntegerTerm::var(Variable(10_000));
        let mut shared = IntegerTerm::var(Variable(20_000));
        for index in 1..size {
            distinct =
                IntegerTerm::add(distinct, IntegerTerm::var(Variable(10_000 + index as u64)));
        }
        for _ in 0..size {
            shared = IntegerTerm::add(shared.clone(), shared.clone());
        }
        for (expression, measurements, is_shared) in [
            (distinct, &mut distinct_work, false),
            (shared, &mut shared_work, true),
        ] {
            let goal = proposition(ConditionTerm::integer_less_equal(
                expression,
                IntegerTerm::constant_i64(0),
            ));
            let (result, work) =
                crate::instrumentation::measure_deterministic_work(|| claim(&goal));
            if is_shared {
                assert_eq!(
                    result.terms,
                    BTreeMap::from([(
                        IntegerAffineAtom::Variable(Variable(20_000)),
                        BigInt::one() << size
                    )])
                );
            } else {
                assert_eq!(result.terms.len(), size);
                assert!(
                    result
                        .terms
                        .values()
                        .all(|coefficient| coefficient == &BigInt::one())
                );
            }
            measurements.push(work);
        }
    }
    for pair in distinct_work.windows(2) {
        assert!(pair[1] <= 3 * pair[0], "{distinct_work:?}");
    }
    for pair in shared_work.windows(2) {
        assert!(
            pair[1] <= 5 * pair[0],
            "growing coefficient bit lengths: {shared_work:?}"
        );
    }
}

#[test]
fn repeated_fold_atoms_share_scoped_alpha_work() {
    let mut work = Vec::new();
    for depth in [8usize, 16, 32, 64] {
        let item = Variable(500 + depth as u64);
        let accumulator = Variable(600 + depth as u64);
        let mut body = machine_fold_body(accumulator.0, item.0);
        for _ in 0..depth {
            let shared: crate::kernel::SharedIntegerTerm = body.clone().into();
            body = IntegerTerm::add(body, shared.as_ref().clone());
        }
        let fold = int32_fold(0, 8, accumulator.0, item.0, body);
        let expression = IntegerTerm::add(fold.clone(), fold);
        let goal = proposition(ConditionTerm::IntegerEqual(
            expression.into(),
            IntegerTerm::constant_i64(0).into(),
        ));
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| claim(&goal));
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(pair[1] <= pair[0] * 3 + 64, "fold affine work: {work:?}");
    }
}

#[test]
fn selected_fold_premises_reuse_one_certificate_scoped_key() {
    let mut work = Vec::new();
    for size in [8usize, 16, 32, 64] {
        let accumulator = Variable(800 + size as u64);
        let item = Variable(900 + size as u64);
        let mut body = machine_fold_body(accumulator.0, item.0);
        for _ in 0..size {
            let shared: crate::kernel::SharedIntegerTerm = body.clone().into();
            body = IntegerTerm::add(shared.as_ref().clone(), body);
        }
        let fold = int32_fold(0, 8, accumulator.0, item.0, body);
        let mut premises = Vec::with_capacity(size);
        let mut nodes = Vec::with_capacity(size);
        for index in 0..size {
            let proposition = proposition(ConditionTerm::IntegerLessEqual(
                fold.clone().into(),
                IntegerTerm::constant_i64(index as i64).into(),
            ));
            let result = claim(&proposition);
            premises.push(proposition);
            nodes.push(IntegerArithmeticNode::Premise { index, result });
        }
        let goal = premises[0].clone();
        let certificate = IntegerArithmeticCertificate {
            nodes,
            conclusion: 0,
        };
        reset_fold_alpha_constructions();
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            certificate.check(&goal, &premises).unwrap();
        });
        assert_eq!(
            fold_alpha_constructions(),
            1,
            "fold key rebuilt per certificate"
        );
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3 + 64,
            "certificate fold-key work: {work:?}"
        );
    }
}

#[test]
fn repeated_large_premise_references_use_cached_normalization() {
    let x = variable(9);
    let mut expression = x;
    for _ in 0..256 {
        expression = IntegerTerm::Add(
            crate::kernel::SharedIntegerTerm::from(expression),
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(1)),
        );
    }
    let shared_premise = proposition(ConditionTerm::IntegerLessEqual(
        crate::kernel::SharedIntegerTerm::from(expression),
        crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(0)),
    ));
    let expected = claim(&shared_premise);
    let shared_nodes = (0..32)
        .map(|_| IntegerArithmeticNode::Premise {
            index: 0,
            result: expected.clone(),
        })
        .collect();
    let shared_certificate = IntegerArithmeticCertificate {
        nodes: shared_nodes,
        conclusion: 31,
    };
    let (_, shared_work) = crate::instrumentation::measure_deterministic_work(|| {
        shared_certificate.check(&shared_premise, std::slice::from_ref(&shared_premise))
    });

    let distinct_premises = (0..32).map(|_| shared_premise.clone()).collect::<Vec<_>>();
    let distinct_nodes = (0..32)
        .map(|index| IntegerArithmeticNode::Premise {
            index,
            result: expected.clone(),
        })
        .collect();
    let distinct_certificate = IntegerArithmeticCertificate {
        nodes: distinct_nodes,
        conclusion: 31,
    };
    let (_, distinct_work) = crate::instrumentation::measure_deterministic_work(|| {
        distinct_certificate.check(&shared_premise, &distinct_premises)
    });

    assert!(shared_work.saturating_mul(4) < distinct_work);
}
