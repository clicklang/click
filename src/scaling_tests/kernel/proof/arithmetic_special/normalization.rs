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
fn float_scale_checks_one_cited_bound_as_related_and_unrelated_bounds_grow() {
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
    let scaled = MachineTerm::float32_binary(
        x.clone(),
        MachineTerm::constant(0.5f32.to_bits()),
        FloatBinaryOperator::Multiply,
    );
    let goal = bound(scaled, -5.0);
    let premise = bound(x.clone(), -10.0);
    let weaker = bound(x.clone(), -11.0);
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
                normalize_using_conditions(&goal, std::slice::from_ref(&premise), &facts)
            });
            hit.unwrap();
            let (miss, miss_work) = crate::instrumentation::measure_deterministic_work(|| {
                normalize_using_conditions(&goal, std::slice::from_ref(&weaker), &facts)
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
