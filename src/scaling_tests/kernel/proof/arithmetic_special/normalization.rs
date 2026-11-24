use super::*;
use crate::kernel::proof::PureFactStore;
use crate::kernel::proof::fact_reasoning::normalize_using_conditions;

#[test]
fn specialized_normalization_uses_only_selected_inputs_as_related_and_unrelated_facts_grow() {
    let v = |n| IntegerTerm::var(crate::kernel::Variable(n));
    let le = |a: IntegerTerm, b: IntegerTerm| {
        Proposition::condition_is(ConditionTerm::IntegerLessEqual(a.into(), b.into()), true)
    };
    let (a, b, f) = (v(877001), v(877002), v(877003));
    let selected = vec![
        le(a.clone(), b.clone()),
        le(f.clone(), IntegerTerm::constant_i64(0)),
    ];
    let goal = le(
        IntegerTerm::multiply(b.clone(), f.clone()),
        IntegerTerm::multiply(a.clone(), f),
    );
    for related in [false, true] {
        let samples = [4, 16, 64].map(|size| {
            let mut ambient = selected.clone();
            for index in 0..size {
                ambient.push(le(
                    v(if related { 877001 } else { 878000 + index }),
                    IntegerTerm::constant_i64(1000 + index as i64),
                ));
            }
            let facts = PureFactStore::from_ordered(&ambient);
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                normalize_using_conditions(&goal, &selected, &facts)
            });
            result.unwrap();
            assert!(normalize_using_conditions(&goal, &selected[..1], &facts).is_err());
            work
        });
        assert!(
            samples[0] > 0 && samples.iter().all(|work| *work <= samples[0] + 8),
            "{related}: {samples:?}"
        );
    }
}

#[test]
fn shifted_one_uses_one_cited_bound_as_related_and_unrelated_bounds_grow() {
    let word = |index| MachineTerm::Variable(crate::kernel::Variable(index));
    let count = word(879001);
    let bound = |value, limit| {
        Proposition::condition_is(
            ConditionTerm::unsigned_less_than(value, MachineTerm::constant(limit)),
            true,
        )
    };
    let goal = Proposition::condition_is(
        ConditionTerm::machine_compare(
            MachineIntegerType::UInt32,
            CompareRelation::Equal,
            MachineTerm::uint32_shift_left(MachineTerm::constant(1), count.clone()),
            MachineTerm::constant(0),
        ),
        false,
    );
    let selected = [bound(count.clone(), 32)];
    let wrong = [bound(count.clone(), 33)];
    for related in [false, true] {
        let samples = [4, 16, 64].map(|size| {
            let mut ambient = vec![selected[0].clone(), wrong[0].clone()];
            for index in 0..size {
                let value = if related {
                    count.clone()
                } else {
                    word(879010 + u64::from(index))
                };
                ambient.push(bound(value, 33 + index));
            }
            let facts = PureFactStore::from_ordered(&ambient);
            let (hit, hit_work) = crate::instrumentation::measure_deterministic_work(|| {
                normalize_using_conditions(&goal, &selected, &facts)
            });
            hit.unwrap();
            let (miss, miss_work) = crate::instrumentation::measure_deterministic_work(|| {
                normalize_using_conditions(&goal, &wrong, &facts)
            });
            assert!(miss.is_err());
            (hit_work, miss_work)
        });
        assert!(
            samples
                .iter()
                .all(|(hit, miss)| *hit <= samples[0].0 + 8 && *miss <= samples[0].1 + 8),
            "{related}: {samples:?}"
        );
    }
}

#[test]
fn float_literal_operations_check_one_cited_bound_as_ambient_bounds_grow() {
    use crate::kernel::{FloatBinaryOperator, Variable};

    let x = MachineTerm::var(Variable(880001));
    let bound = |value, limit: f32| {
        Proposition::condition_is(
            ConditionTerm::float32_compare(
                value,
                MachineTerm::constant(limit.to_bits()),
                ComparisonOperator::GreaterEqual,
            ),
            true,
        )
    };
    let goals = [
        (FloatBinaryOperator::Multiply, 0.5f32, -5.0),
        (FloatBinaryOperator::Add, 1.0f32, -9.0),
        (FloatBinaryOperator::Divide, 2.0f32, -5.0),
        (FloatBinaryOperator::Subtract, 2.0f32, -12.0),
    ]
    .map(|(operation, literal, endpoint)| {
        let result = MachineTerm::float32_binary(
            x.clone(),
            MachineTerm::constant(literal.to_bits()),
            operation,
        );
        bound(result, endpoint)
    });
    let premise = bound(x.clone(), -10.0);
    let weaker = bound(x.clone(), -11.0);
    for goal in &goals {
        for related in [false, true] {
            let samples = [4, 16, 64].map(|size| {
                let mut ambient = vec![premise.clone(), weaker.clone()];
                for index in 0..size {
                    let value = if related {
                        x.clone()
                    } else {
                        MachineTerm::var(Variable(880010 + index))
                    };
                    ambient.push(bound(value, -20.0 - index as f32));
                }
                let facts = PureFactStore::from_ordered(&ambient);
                let (hit, hit_work) = crate::instrumentation::measure_deterministic_work(|| {
                    normalize_using_conditions(goal, std::slice::from_ref(&premise), &facts)
                });
                hit.unwrap();
                let (miss, miss_work) = crate::instrumentation::measure_deterministic_work(|| {
                    normalize_using_conditions(goal, std::slice::from_ref(&weaker), &facts)
                });
                assert!(miss.is_err());
                (hit_work, miss_work)
            });
            assert!(
                samples
                    .iter()
                    .all(|(hit, miss)| *hit <= samples[0].0 + 8 && *miss <= samples[0].1 + 8),
                "{related}: {samples:?}"
            );
        }
    }
}

#[test]
fn float_pair_checks_two_cited_bounds_as_ambient_bounds_grow() {
    use crate::kernel::{FloatBinaryOperator, Variable};

    let x = MachineTerm::var(Variable(880401));
    let y = MachineTerm::var(Variable(880402));
    let bound = |value, endpoint: f32, operator| {
        Proposition::condition_is(
            ConditionTerm::float32_compare(
                value,
                MachineTerm::constant(endpoint.to_bits()),
                operator,
            ),
            true,
        )
    };
    let ge = ComparisonOperator::GreaterEqual;
    let le = ComparisonOperator::LessEqual;
    for (operator, direction, endpoint, weaker) in [
        (FloatBinaryOperator::Add, ge, 10.0, 9.0),
        (FloatBinaryOperator::Subtract, le, -10.0, -9.0),
    ] {
        let goal = bound(
            MachineTerm::float32_binary(x.clone(), y.clone(), operator),
            0.0,
            ge,
        );
        let first = bound(x.clone(), -10.0, ge);
        let selected = [first.clone(), bound(y.clone(), endpoint, direction)];
        let insufficient = [first, bound(y.clone(), weaker, direction)];
        for related in [false, true] {
            let samples = [4, 16, 64].map(|size| {
                let mut ambient = selected.to_vec();
                ambient.push(insufficient[1].clone());
                for index in 0..size {
                    let value = if related {
                        x.clone()
                    } else {
                        MachineTerm::var(Variable(880410 + index))
                    };
                    ambient.push(bound(value, -20.0 - index as f32, ge));
                }
                let facts = PureFactStore::from_ordered(&ambient);
                let (hit, hit_work) = crate::instrumentation::measure_deterministic_work(|| {
                    normalize_using_conditions(&goal, &selected, &facts)
                });
                let (miss, miss_work) = crate::instrumentation::measure_deterministic_work(|| {
                    normalize_using_conditions(&goal, &insufficient, &facts)
                });
                hit.unwrap();
                assert!(miss.is_err());
                (hit_work, miss_work)
            });
            assert!(
                samples
                    .iter()
                    .all(|(hit, miss)| *hit <= samples[0].0 + 8 && *miss <= samples[0].1 + 8),
                "{related}: {samples:?}"
            );
        }
    }
}

#[test]
fn float_narrowing_checks_one_cited_bound_as_ambient_bounds_grow() {
    use crate::kernel::Variable;

    let x = MachineTerm::var(Variable(880501));
    let source = |value, endpoint: f64| {
        Proposition::condition_is(
            ConditionTerm::float64_compare(
                value,
                MachineTerm::uint64_constant(endpoint.to_bits()),
                ComparisonOperator::LessEqual,
            ),
            true,
        )
    };
    let goal = Proposition::condition_is(
        ConditionTerm::float32_compare(
            MachineTerm::opaque_conversion("c_float64_to_float32", x.clone()),
            MachineTerm::constant(1f32.to_bits()),
            ComparisonOperator::LessEqual,
        ),
        true,
    );
    let selected = [source(x.clone(), 1.0 + f64::EPSILON)];
    let insufficient = [source(x.clone(), 2.0)];
    for related in [false, true] {
        let samples = [4, 16, 64].map(|size| {
            let mut ambient = vec![selected[0].clone(), insufficient[0].clone()];
            for index in 0..size {
                let value = if related {
                    x.clone()
                } else {
                    MachineTerm::var(Variable(880510 + index))
                };
                ambient.push(source(value, 3.0 + index as f64));
            }
            let facts = PureFactStore::from_ordered(&ambient);
            let (hit, hit_work) = crate::instrumentation::measure_deterministic_work(|| {
                normalize_using_conditions(&goal, &selected, &facts)
            });
            let (miss, miss_work) = crate::instrumentation::measure_deterministic_work(|| {
                normalize_using_conditions(&goal, &insufficient, &facts)
            });
            hit.unwrap();
            assert!(miss.is_err());
            (hit_work, miss_work)
        });
        assert!(
            samples
                .iter()
                .all(|(hit, miss)| *hit <= samples[0].0 + 8 && *miss <= samples[0].1 + 8),
            "{related}: {samples:?}"
        );
    }
}

#[test]
fn negative_product_guard_checks_only_cited_signs_and_quotient() {
    let ty = MachineIntegerType::Int32;
    let observe = |term| IntegerTerm::from_machine(ty, term).unwrap();
    let x = MachineTerm::var(crate::kernel::Variable(880601));
    let y = MachineTerm::var(crate::kernel::Variable(880602));
    let max = MachineTerm::constant(i32::MAX as u32);
    let quotient = observe(MachineTerm::machine_binary(
        ty,
        MachineBinaryOp::Divide,
        max.clone(),
        y.clone(),
    ));
    let x = observe(x);
    let y = observe(y);
    let zero = IntegerTerm::constant_i64(0);
    let fact = |condition| Proposition::condition_is(condition, true);
    let goal = fact(ConditionTerm::integer_less_equal(
        IntegerTerm::multiply(x.clone(), y.clone()),
        observe(max),
    ));
    let selected = [
        fact(ConditionTerm::integer_less_than(x.clone(), zero.clone())),
        fact(ConditionTerm::integer_less_than(y, zero)),
        Proposition::condition_is(ConditionTerm::integer_less_than(x.clone(), quotient), false),
    ];
    for related in [false, true] {
        let samples = [4, 16, 64].map(|size| {
            let mut ambient = selected.to_vec();
            for index in 0..size {
                let value = if related {
                    x.clone()
                } else {
                    observe(MachineTerm::var(crate::kernel::Variable(880610 + index)))
                };
                ambient.push(fact(ConditionTerm::integer_greater_equal(
                    value,
                    IntegerTerm::constant_i64(-100 - index as i64),
                )));
            }
            let facts = PureFactStore::from_ordered(&ambient);
            let (hit, hit_work) = crate::instrumentation::measure_deterministic_work(|| {
                normalize_using_conditions(&goal, &selected, &facts)
            });
            let (miss, miss_work) = crate::instrumentation::measure_deterministic_work(|| {
                normalize_using_conditions(&goal, &selected[..2], &facts)
            });
            hit.unwrap();
            assert!(miss.is_err());
            (hit_work, miss_work)
        });
        assert!(
            samples
                .iter()
                .all(|(hit, miss)| *hit <= samples[0].0 + 8 && *miss <= samples[0].1 + 8),
            "{related}: {samples:?}"
        );
    }
}

#[test]
fn float_quotient_range_checks_only_four_cited_endpoints() {
    use crate::kernel::{FloatBinaryOperator, Variable};

    let x = MachineTerm::var(Variable(880701));
    let y = MachineTerm::var(Variable(880702));
    let bound = |word, endpoint: f32, relation| {
        Proposition::condition_is(
            ConditionTerm::float32_compare(
                word,
                MachineTerm::constant(endpoint.to_bits()),
                relation,
            ),
            true,
        )
    };
    let ge = ComparisonOperator::GreaterEqual;
    let le = ComparisonOperator::LessEqual;
    let goal = bound(
        MachineTerm::float32_binary(x.clone(), y.clone(), FloatBinaryOperator::Divide),
        0.0,
        le,
    );
    let selected = [
        bound(x.clone(), 1.0, ge),
        bound(y.clone(), -2.0, ge),
        bound(x.clone(), 2.0, le),
        bound(y, -1.0, le),
    ];
    for related in [false, true] {
        let samples = [4, 16, 64].map(|size| {
            let mut ambient = selected.to_vec();
            for index in 0..size {
                let value = if related {
                    x.clone()
                } else {
                    MachineTerm::var(Variable(880710 + index))
                };
                ambient.push(bound(value, 3.0 + index as f32, le));
            }
            let facts = PureFactStore::from_ordered(&ambient);
            let (hit, hit_work) = crate::instrumentation::measure_deterministic_work(|| {
                normalize_using_conditions(&goal, &selected, &facts)
            });
            let (miss, miss_work) = crate::instrumentation::measure_deterministic_work(|| {
                normalize_using_conditions(&goal, &selected[..3], &facts)
            });
            hit.unwrap();
            assert!(miss.is_err());
            (hit_work, miss_work)
        });
        assert!(
            samples
                .iter()
                .all(|(hit, miss)| *hit <= samples[0].0 + 8 && *miss <= samples[0].1 + 8),
            "{related}: {samples:?}"
        );
    }
}
