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
fn affine_claims_read_retained_fold_operands_without_export() {
    use crate::kernel::{
        KernelFold, KernelFoldIndex, KernelIntegerOperator, KernelTermExport, KernelType,
        StoredConditionTerm,
    };
    let mut samples = Vec::new();
    let mut disequality_samples = Vec::new();
    for depth in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let fold = |accumulator, end| {
            let acc = Variable(accumulator);
            let mut body = KernelTerm::variable(KernelType::Integer, acc);
            for _ in 0..depth {
                body = KernelTerm::integer_operation(
                    KernelIntegerOperator::Add,
                    vec![body.clone(), body],
                )
                .unwrap();
            }
            let zero = KernelTerm::integer_literal(0.into());
            KernelFold::new(
                KernelFoldIndex::Integer,
                acc,
                Variable(accumulator + 1),
                [
                    zero.clone(),
                    KernelTerm::integer_literal(BigInt::from(end)),
                    zero,
                    body,
                ],
            )
            .unwrap()
            .into_term()
        };
        let left = fold(90_000, 8);
        let right = fold(90_002, 8);
        let different = fold(90_006, 9);
        let comparison = |operator, right| {
            KernelTerm::integer_comparison(operator, [left.clone(), right]).unwrap()
        };
        let stored = |root| StoredConditionTerm::from_root(root).unwrap();
        let equal = Proposition::condition_is(
            stored(comparison(IntegerComparisonOperator::Equal, right.clone())),
            true,
        );
        let disequal = Proposition::condition_is(
            stored(comparison(
                IntegerComparisonOperator::NotEqual,
                different.clone(),
            )),
            true,
        );
        let exports = KernelTermExport::integer_export_count();
        let (differences, work) = crate::instrumentation::measure_deterministic_work(|| {
            integer_disequality_claims(&disequal)
        });
        assert_eq!(differences.len(), 1);
        assert_eq!(differences[0].terms.len(), 2);
        assert!(excluded_type_bound(&disequal).is_none());
        assert_eq!(KernelTermExport::integer_export_count(), exports);
        disequality_samples.push(work);
        let works = [0, 16, 64, 256].map(|unrelated| {
            let mut context = IntegerAffineCollectionContext::default();
            context
                .constants
                .extend((0..unrelated).map(|id| (id, None)));
            let exports = KernelTermExport::integer_export_count();
            let (claims, work) = crate::instrumentation::measure_deterministic_work(|| {
                integer_affine_claims_with_context(&equal, &mut context)
            });
            assert_eq!(claims.len(), 1);
            assert!(claims[0].terms.is_empty());
            assert!(claims[0].constant.is_zero());
            assert!(written_integer_affine_claim(&equal));
            assert!(integer_affine_machine_values(&equal).is_empty());
            assert_eq!(KernelTermExport::integer_export_count(), exports);
            work
        });
        assert!(
            works.iter().max().unwrap() - works.iter().min().unwrap() <= 16,
            "{works:?}"
        );
        samples.push(works[0]);

        for operator in [
            IntegerComparisonOperator::Equal,
            IntegerComparisonOperator::NotEqual,
            IntegerComparisonOperator::LessThan,
            IntegerComparisonOperator::LessEqual,
            IntegerComparisonOperator::GreaterThan,
            IntegerComparisonOperator::GreaterEqual,
        ] {
            for operand in [
                right.clone(),
                different.clone(),
                KernelTerm::integer_literal(3.into()),
                KernelTerm::variable(KernelType::Integer, Variable(90_004)),
            ] {
                let root = comparison(operator, operand);
                let native = KernelTermExport::condition(&root).unwrap();
                for value in [true, false] {
                    let native = Proposition::condition_is(native.clone(), value);
                    let retained = Proposition::condition_is(stored(root.clone()), value);
                    let expected = integer_affine_claim(&native);
                    let expected_differences = integer_disequality_claims(&native);
                    let expected_negated =
                        integer_disequality_claims(&Proposition::Not(Box::new(native)));
                    let exports = KernelTermExport::integer_export_count();
                    let actual = integer_affine_claim(&retained);
                    assert_eq!(actual, expected, "{operator:?}, {value}");
                    assert_eq!(integer_disequality_claims(&retained), expected_differences);
                    assert_eq!(
                        integer_disequality_claims(&Proposition::Not(Box::new(retained))),
                        expected_negated
                    );
                    assert_eq!(KernelTermExport::integer_export_count(), exports);
                }
            }
        }
    }
    for samples in [samples, disequality_samples] {
        for pair in samples.windows(2) {
            assert!(pair[1] <= 4 * pair[0] + 64, "{samples:?}");
        }
    }
}

#[test]
fn shared_additive_fold_claims_stay_retained() {
    use crate::kernel::{KernelTermExport, KernelTermImport};
    use KernelIntegerOperator as Op;
    let mut samples = Vec::new();
    for depth in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let fold = int32_fold(0, 8, 91_000, 91_001, machine_fold_body(91_000, 91_001));
        let root = KernelTermImport::default().integer(&fold.into());
        let operation =
            |operator, children| KernelTerm::integer_operation(operator, children).unwrap();
        let mut expression = root.clone();
        for _ in 0..depth {
            // This DAG has exponentially many paths. Its net fold weight
            // stays one, so coefficient bit lengths do not dominate work.
            let twice = operation(Op::Add, vec![expression.clone(), expression.clone()]);
            let difference = operation(Op::Subtract, vec![expression, twice]);
            expression = operation(Op::Negate, vec![difference]);
        }
        let expression = operation(
            Op::Add,
            vec![expression, KernelTerm::integer_literal(3.into())],
        );
        let comparison =
            KernelTerm::integer_comparison(IntegerComparisonOperator::Equal, [expression, root])
                .unwrap();
        let condition = StoredConditionTerm::from_root(comparison.clone()).unwrap();
        let equal = Proposition::condition_is(condition.clone(), true);
        let disequal = Proposition::condition_is(condition, false);
        let exports = KernelTermExport::integer_export_count();
        assert!(
            crate::instrumentation::with_run_work_limit(8, || integer_affine_claim(&equal))
                .is_none()
        );
        assert!(
            crate::instrumentation::with_run_work_limit(8, || integer_disequality_claims(
                &disequal
            ))
            .is_empty()
        );
        assert_eq!(KernelTermExport::integer_export_count(), exports);
        let works = [0, 16, 64, 256].map(|unrelated| {
            let mut context = IntegerAffineCollectionContext::default();
            context
                .constants
                .extend((0..unrelated).map(|id| (id, None)));
            let exports = KernelTermExport::integer_export_count();
            let (claim, work) = crate::instrumentation::measure_deterministic_work(|| {
                integer_affine_claim_with_context(&equal, &mut context).unwrap()
            });
            assert!(claim.terms.is_empty());
            assert_eq!(claim.constant, BigInt::from(3));
            assert!(integer_disequality_claims(&disequal).is_empty());
            assert!(excluded_type_bound(&disequal).is_none());
            assert!(integer_affine_machine_values(&equal).is_empty());
            assert_eq!(KernelTermExport::integer_export_count(), exports);
            work
        });
        assert!(
            works.iter().max().unwrap() - works.iter().min().unwrap() <= 16,
            "{works:?}"
        );
        samples.push(works[0]);

        let native = KernelTermExport::condition(&comparison).unwrap();
        for value in [false, true] {
            let native = Proposition::condition_is(native.clone(), value);
            let retained = if value { &equal } else { &disequal };
            assert_eq!(
                integer_affine_claim(&native),
                integer_affine_claim(retained)
            );
            assert_eq!(
                integer_disequality_claims(&native),
                integer_disequality_claims(retained)
            );
        }
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= 4 * pair[0] + 64, "{samples:?}");
    }
}

#[test]
fn constant_arithmetic_checking_visits_shared_nodes_once_and_bounds_squaring() {
    use crate::kernel::SharedIntegerTerm;
    let mut costs = Vec::new();
    for depth in [16, 32, 64, 128] {
        let mut value = SharedIntegerTerm::from(IntegerTerm::constant_i64(1));
        for _ in 0..depth {
            value = IntegerTerm::Add(value.clone(), value).into();
        }
        let mut cache = HashMap::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            collect_integer_constants(&value, &mut cache).unwrap();
        });
        assert_eq!(cache.len(), depth + 1);
        assert_eq!(
            cache.get(&value.id()).unwrap().as_ref().unwrap(),
            &(BigInt::from(1) << depth)
        );
        costs.push(work);
        let (_, repeated) = crate::instrumentation::measure_deterministic_work(|| {
            collect_integer_constants(&value, &mut cache).unwrap();
        });
        assert!(repeated < 8, "{repeated}");
    }
    // The result's bit length grows with depth; numeric work may be
    // quadratic in depth, but never exponential in the unshared tree size.
    for pair in costs.windows(2) {
        assert!(pair[1] < 5 * pair[0], "{costs:?}");
    }
    let mut value = SharedIntegerTerm::from(IntegerTerm::constant_i64(2));
    for _ in 0..64 {
        value = IntegerTerm::Multiply(value.clone(), value).into();
    }
    let limits = crate::instrumentation::TacticWorkLimits {
        simple: 1000,
        smart: 1000,
        control: 1000,
    };
    let result = crate::instrumentation::with_tactic_work_limits(limits, || {
        collect_integer_constants(&value, &mut HashMap::new())
    });
    assert!(
        result.is_none(),
        "checking must refuse before evaluating a giant numeral"
    );
}
