// Scaling tests of `src/kernel/proof/fact_reasoning.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

#[test]
fn quantified_single_match_does_not_check_the_whole_alpha_bucket() {
    let quantified = |name: String| Proposition::ForAll {
        name: Default::default(),
        var: Variable(1),
        sort: Sort::ProgramInt32,
        body: Box::new(Proposition::Exists {
            name,
            var: Variable(2),
            sort: Sort::ProgramInt32,
            body: Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    MachineTerm::Variable(Variable(1)),
                    MachineTerm::Variable(Variable(2)),
                ),
                true,
            )),
        }),
    };
    let goal = quantified("goal".into());
    let mut curve = Vec::new();
    for size in [8, 16, 32, 64] {
        let facts = PureFactStore::from_ordered(
            &(0..size)
                .map(|i| quantified(format!("witness{i}")))
                .collect::<Vec<_>>(),
        );
        assert_eq!(
            facts.quantified_bucket_len(&quantified_equivalence_index_key(&goal).unwrap()),
            Some(size)
        );
        let (matched, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.matching_quantified_fact(&goal)
        });
        assert!(matched.is_some());
        curve.push(work);
    }
    assert!(curve[0] > 0);
    assert!(
        curve.iter().all(|work| *work == curve[0]),
        "single-match bucket work: {curve:?}"
    );
}

#[test]
fn quantified_nested_matching_work_is_linear_and_context_indexed() {
    let nested = |depth: usize, base: u64| {
        let mut p = Proposition::ConditionIs(
            ConditionTerm::equal(
                MachineTerm::Variable(Variable(base)),
                MachineTerm::constant(0),
            ),
            true,
        );
        for index in (0..depth).rev() {
            p = Proposition::ForAll {
                name: Default::default(),
                var: Variable(base + index as u64),
                sort: Sort::ProgramInt32,
                body: Box::new(p),
            };
        }
        p
    };
    let mut depths = Vec::new();
    let mut contexts = Vec::new();
    for size in [8, 16, 32, 64] {
        // Compare cold contexts; a preceding size must not warm this query.
        let _session = crate::kernel::VerificationSession::enter();
        let left = nested(size, 100);
        let right = nested(size, 1000);
        let (matches, work) = crate::instrumentation::measure_deterministic_work(|| {
            quantified_binder_equivalent(&left, &right)
        });
        assert!(matches);
        depths.push(work);
        let mut facts = PureFactStore::from_ordered(&[nested(2, 100)]);
        for index in 0..size {
            facts = facts.with_fact(Proposition::ForAll {
                name: Default::default(),
                var: Variable(9000),
                sort: Sort::ProgramInt32,
                body: Box::new(Proposition::ConditionIs(
                    ConditionTerm::equal(
                        MachineTerm::Variable(Variable(9000)),
                        MachineTerm::constant(index as u32 + 1),
                    ),
                    true,
                )),
            });
        }
        let goal = nested(2, 1000);
        let (matches, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.matching_quantified_fact(&goal).is_some()
        });
        assert!(matches);
        contexts.push(work);
    }
    assert!(depths[0] > 0);
    for pair in depths.windows(2) {
        assert!(pair[1] <= pair[0] * 2, "binder work: {depths:?}");
    }
    assert!(
        contexts.iter().all(|work| *work == contexts[0]),
        "unrelated context work: {contexts:?}"
    );
}

#[test]
fn machine_affine_equality_work_is_linear_in_the_sum() {
    // `v0 + ... + vn == vn + ... + v0` at 64 bits: the affine comparison
    // visits each node once, so quadrupling the operands at most about
    // quadruples the work.
    let mut costs = Vec::new();
    for size in [16u64, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = |index: u64| MachineTerm::Variable(Variable(97_000 + index));
        let sum = |order: &mut dyn Iterator<Item = u64>| {
            let first = variable(order.next().unwrap());
            order.fold(first, |sum, index| MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Add,
                left: Box::new(sum),
                right: Box::new(variable(index)),
            })
        };
        let forward = sum(&mut (0..size));
        let backward = sum(&mut (0..size).rev());
        let goal = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: Box::new(forward),
                right: Box::new(backward),
            },
            true,
        );
        let (proved, work) =
            crate::instrumentation::measure_deterministic_work(|| normalizes_context_free(&goal));
        assert!(proved);
        costs.push(work);
    }
    assert!(
        costs[0] > 0 && costs.windows(2).all(|pair| pair[1] <= pair[0] * 6),
        "{costs:?}"
    );
}

#[test]
fn integer_affine_equality_work_is_linear_in_the_sum() {
    // The exact `Integer` counterpart: `v0 + ... + vn == vn + ... + v0`.
    let mut costs = Vec::new();
    for size in [16u64, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = |index: u64| IntegerTerm::Variable(Variable(98_000 + index));
        let sum = |order: &mut dyn Iterator<Item = u64>| {
            let first = variable(order.next().unwrap());
            order.fold(first, |sum, index| IntegerTerm::add(sum, variable(index)))
        };
        let forward: SharedIntegerTerm = sum(&mut (0..size)).into();
        let backward: SharedIntegerTerm = sum(&mut (0..size).rev()).into();
        let goal = Proposition::ConditionIs(ConditionTerm::IntegerEqual(forward, backward), true);
        let (proved, work) =
            crate::instrumentation::measure_deterministic_work(|| normalizes_context_free(&goal));
        assert!(proved);
        costs.push(work);
    }
    assert!(
        costs[0] > 0 && costs.windows(2).all(|pair| pair[1] <= pair[0] * 6),
        "{costs:?}"
    );
}

#[test]
fn integer_affine_comparison_work_is_linear_in_a_shared_term_dag() {
    // `a_d = a_{d-1} + a_{d-1}` is a DAG of `d` nodes with `2^d` paths: the
    // comparison `a_d + 1 > a_d` visits each node once, not each path.
    let mut costs = Vec::new();
    for depth in [16u64, 32, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut term = IntegerTerm::Variable(Variable(99_000));
        for _ in 0..depth {
            let shared: SharedIntegerTerm = term.into();
            term = IntegerTerm::Add(shared.clone(), shared);
        }
        let side: SharedIntegerTerm = term.into();
        let successor: SharedIntegerTerm =
            IntegerTerm::add(side.as_ref().clone(), IntegerTerm::constant_i64(1)).into();
        let goal =
            Proposition::ConditionIs(ConditionTerm::IntegerGreaterThan(successor, side), true);
        let (proved, work) =
            crate::instrumentation::measure_deterministic_work(|| normalizes_context_free(&goal));
        assert!(proved);
        costs.push(work);
    }
    assert!(
        costs[0] > 0 && costs.windows(2).all(|pair| pair[1] <= pair[0] * 3),
        "{costs:?}"
    );
}

#[test]
fn integer_coefficient_normalization_work_scales_with_selected_terms() {
    let mut costs = Vec::new();
    for size in [16u64, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut sum = IntegerTerm::constant_i64(0);
        let mut distributed = IntegerTerm::constant_i64(0);
        for index in 0..size {
            let value = IntegerTerm::Variable(Variable(991_000 + index));
            sum = IntegerTerm::add(sum, value.clone());
            distributed = IntegerTerm::add(
                distributed,
                IntegerTerm::multiply(IntegerTerm::constant_i64(7), value),
            );
        }
        let goal = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(
                IntegerTerm::multiply(IntegerTerm::constant_i64(7), sum).into(),
                distributed.into(),
            ),
            true,
        );
        let (proved, work) =
            crate::instrumentation::measure_deterministic_work(|| normalizes_context_free(&goal));
        assert!(proved);
        costs.push(work);
    }
    assert!(
        costs[0] > 0 && costs.windows(2).all(|pair| pair[1] <= 6 * pair[0]),
        "coefficient normalization rescanned its input: {costs:?}"
    );
}

#[test]
fn integer_coefficient_normalization_visits_shared_nodes_once() {
    let mut costs = Vec::new();
    for depth in [16u64, 32, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut value: SharedIntegerTerm = IntegerTerm::Variable(Variable(992_001)).into();
        for _ in 0..depth {
            value = IntegerTerm::Add(value.clone(), value).into();
        }
        let left = IntegerTerm::Multiply(IntegerTerm::constant_i64(3).into(), value.clone()).into();
        let right =
            IntegerTerm::Add(value.clone(), IntegerTerm::Add(value.clone(), value).into()).into();
        let goal = Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true);
        let (proved, work) =
            crate::instrumentation::measure_deterministic_work(|| normalizes_context_free(&goal));
        assert!(proved);
        costs.push(work);
    }
    assert!(
        costs[0] > 0 && costs.windows(2).all(|pair| pair[1] <= 3 * pair[0]),
        "coefficient normalization expanded shared paths: {costs:?}"
    );
}

include!("intrinsic_normalization_tests.rs");

#[test]
fn footprint_normalization_does_not_scan_ambient_aliases_or_separations() {
    check_footprint_normalization_scaling([4, 8, 16, 32]);
}

#[test]
#[ignore = "nightly: footprint normalization with 512 related spans and aliases"]
fn footprint_normalization_ignores_large_alias_and_separation_buckets() {
    check_footprint_normalization_scaling([8, 32, 128, 512]);
}

fn check_footprint_normalization_scaling(sizes: [u64; 4]) {
    let costs = sizes.map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let (goal, separation, alias) = footprint_alias_fixture();
        let mut facts = PureFactStore::from_ordered(&[separation.clone(), alias]);
        let pointer = |id| Pointer::symbolic(Variable(id));
        for i in 0..size {
            // Grow the selected address class and a related separation bucket.
            facts = facts.with_fact(Proposition::ConditionIs(
                ConditionTerm::pointer_equal(pointer(96_140), pointer(97_000 + i)),
                true,
            ));
            let range = |p, bytes: u32| {
                Resource::Memory(MemoryRange::new_with_element_width(
                    p,
                    0u32.into(),
                    bytes.into(),
                    1,
                ))
            };
            facts = facts.with_fact(Proposition::ResourceSeparate {
                left: Box::new(range(pointer(96_140), 1)),
                right: Box::new(range(pointer(96_142), 16 + i as u32)),
            });
            facts = facts.with_fact(Proposition::ConditionIs(
                ConditionTerm::pointer_equal(pointer(99_000 + i * 2), pointer(99_001 + i * 2)),
                true,
            ));
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            normalize_using_conditions(&goal, std::slice::from_ref(&separation), &facts)
        });
        result.unwrap();
        work
    });
    assert!(costs[0] > 0);
    assert!(
        costs.iter().all(|cost| *cost <= costs[0] * 2 + 32),
        "{costs:?}"
    );
}
