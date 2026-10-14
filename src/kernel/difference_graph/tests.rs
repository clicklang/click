use super::*;
use crate::kernel::{PureFactContext, Variable};

thread_local! {
    pub(super) static GRAPH_WORK: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

fn graph_work<R>(operation: impl FnOnce() -> R) -> (R, usize) {
    GRAPH_WORK.with(|work| work.set(0));
    let result = operation();
    (result, GRAPH_WORK.with(std::cell::Cell::get))
}

fn variable(id: u64) -> Bitvector32Term {
    Bitvector32Term::Variable(Variable(91_000 + id))
}

fn constant(value: i32) -> Bitvector32Term {
    Bitvector32Term::Constant(value as u32)
}

fn plus(term: &Bitvector32Term, value: i32) -> Bitvector32Term {
    Bitvector32Term::Add(Box::new(term.clone()), Box::new(constant(value)))
}

fn lt(a: &Bitvector32Term, b: &Bitvector32Term) -> ConditionTerm {
    ConditionTerm::signed_less_than(a.clone(), b.clone())
}

fn le(a: &Bitvector32Term, b: &Bitvector32Term) -> ConditionTerm {
    ConditionTerm::signed_less_equal(a.clone(), b.clone())
}

fn add_overflows(a: &Bitvector32Term, b: &Bitvector32Term) -> ConditionTerm {
    ConditionTerm::Bitvector32SignedAddOverflows(Box::new(a.clone()), Box::new(b.clone()))
}

fn graph(facts: &[(ConditionTerm, bool)]) -> DifferenceGraph {
    let mut graph = DifferenceGraph::new();
    for (condition, value) in facts {
        graph.assume_condition(condition, *value);
    }
    graph
}

#[test]
fn constant_bounds_decide_orders_and_overflow() {
    let i = variable(0);
    let graph = graph(&[(le(&constant(0), &i), true), (lt(&i, &constant(4)), true)]);
    assert_eq!(graph.decide(&lt(&i, &constant(4))), Some(true));
    assert_eq!(graph.decide(&lt(&i, &constant(0))), Some(false));
    assert_eq!(graph.decide(&lt(&i, &constant(3))), None);
    // `i + 1` cannot overflow for `0 <= i < 4`.
    assert_eq!(graph.decide(&add_overflows(&i, &constant(1))), Some(false));
    assert_eq!(graph.decide(&lt(&plus(&i, 1), &constant(5))), Some(true));
}

#[test]
fn relations_between_values_decide_through_paths() {
    let (index, n, length) = (variable(0), variable(1), variable(2));
    let graph = graph(&[(lt(&index, &n), true), (le(&n, &length), true)]);
    assert_eq!(graph.decide(&lt(&index, &length)), Some(true));
    assert_eq!(graph.decide(&le(&length, &index)), Some(false));
    assert_eq!(graph.decide(&lt(&n, &index)), Some(false));
    assert_eq!(graph.decide(&lt(&length, &n)), Some(false));
    assert_eq!(graph.decide(&lt(&n, &length)), None);
}

#[test]
fn a_false_fact_states_its_negation() {
    let (x, y) = (variable(0), variable(1));
    let graph = graph(&[(lt(&x, &y), false)]);
    assert_eq!(graph.decide(&le(&y, &x)), Some(true));
}

#[test]
fn a_sum_is_linked_only_when_it_cannot_wrap() {
    let x = variable(0);
    let max = constant(i32::MAX);
    // Unbounded `x`: `x + 1` may wrap, so it says nothing about `x`.
    let unbounded = graph(&[(lt(&plus(&x, 1), &constant(10)), true)]);
    assert_eq!(unbounded.decide(&lt(&x, &constant(9))), None);
    assert_eq!(unbounded.decide(&add_overflows(&x, &constant(1))), None);
    // Bounded below `INT_MAX`: the sum is exact, and its bound reaches `x`.
    let bounded = graph(&[
        (lt(&x, &max), true),
        (lt(&plus(&x, 1), &constant(10)), true),
    ]);
    assert_eq!(bounded.decide(&lt(&x, &constant(9))), Some(true));
    // A bound that arrives after the sum still links it.
    let late = graph(&[
        (lt(&plus(&x, 1), &constant(10)), true),
        (lt(&x, &max), true),
    ]);
    assert_eq!(late.decide(&lt(&x, &constant(9))), Some(true));
}

/// Only the absence of overflow is answered: a certain overflow stays
/// open, because proof terms that are not C read an undecided overflow as
/// a value (`DifferenceGraph::decide_overflow`).
#[test]
fn overflow_is_decided_at_the_edges_of_the_range() {
    let x = variable(0);
    let near_max = graph(&[(le(&constant(i32::MAX - 1), &x), true)]);
    assert_eq!(near_max.decide(&add_overflows(&x, &constant(2))), None);
    assert_eq!(near_max.decide(&add_overflows(&x, &constant(1))), None);
    let below = graph(&[(le(&x, &constant(i32::MAX - 1)), true)]);
    assert_eq!(below.decide(&add_overflows(&x, &constant(1))), Some(false));
}

#[test]
fn unsigned_conversion_keeps_a_nonnegative_value() {
    let i = variable(0);
    let wide = Bitvector32Term::UInt64From32(Box::new(i.clone()));
    let length = variable(1);
    let below =
        ConditionTerm::Bitvector64UnsignedLessThan(Box::new(wide), Box::new(length.clone()));
    let graph = graph(&[(le(&constant(0), &i), true), (below, true)]);
    let length_positive = ConditionTerm::Bitvector64UnsignedLessThan(
        Box::new(Bitvector32Term::UInt64Constant(0)),
        Box::new(length),
    );
    assert_eq!(graph.decide(&length_positive), Some(true));
}

#[test]
fn contradictions_are_detected_and_decide_no_order() {
    let (x, y) = (variable(0), variable(1));
    let cycle = graph(&[(lt(&x, &y), true), (lt(&y, &x), true)]);
    assert!(cycle.is_contradictory());
    assert_eq!(cycle.decide(&lt(&x, &y)), None);
    let bounds = graph(&[(lt(&x, &constant(3)), true), (lt(&constant(5), &x), true)]);
    assert!(bounds.is_contradictory());
}

#[test]
fn a_clone_is_a_branch() {
    let (x, y) = (variable(0), variable(1));
    let trunk = graph(&[(lt(&x, &y), true)]);
    let mut branch = trunk.clone();
    branch.assume_condition(&lt(&y, &constant(0)), true);
    assert_eq!(branch.decide(&lt(&x, &constant(-1))), Some(true));
    assert_eq!(trunk.decide(&lt(&x, &constant(-1))), None);
}

/// Generated fact sets over three variables bounded to [-4, 4], two constant
/// offsets of them, and constants, against every model: whatever the graph
/// decides holds in every model of the facts, and an order between two pool
/// terms that every model agrees on is decided (difference logic is
/// complete for these facts). The general decision, where it also answers,
/// agrees.
#[test]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn decisions_hold_in_every_model_and_are_complete() {
    let variables = (0..3).map(variable).collect::<Vec<_>>();
    let mut pool = variables.clone();
    pool.push(plus(&variables[0], 1));
    pool.push(plus(&variables[1], -2));
    pool.extend([-2, 0, 3].map(constant));
    let value = |term: &Bitvector32Term, model: &[i128]| -> i128 {
        match term {
            Bitvector32Term::Constant(value) => i128::from(*value as i32),
            Bitvector32Term::Add(base, offset) => {
                let base = variables.iter().position(|v| v == base.as_ref()).unwrap();
                let Bitvector32Term::Constant(offset) = offset.as_ref() else {
                    unreachable!()
                };
                model[base] + i128::from(*offset as i32)
            }
            _ => model[variables.iter().position(|v| v == term).unwrap()],
        }
    };
    let holds = |condition: &ConditionTerm, model: &[i128]| -> bool {
        // The constructors fold a comparison of two constants.
        if let ConditionTerm::Constant(value) = condition {
            return *value;
        }
        let [(_, ref lower, ref upper, strict)] = condition_orders(condition, true)[..] else {
            unreachable!("{condition:?}")
        };
        let (lower, upper) = (value(lower, model), value(upper, model));
        if strict {
            lower < upper
        } else {
            lower <= upper
        }
    };
    let models = (0..9i128.pow(3))
        .map(|index| {
            (0..3)
                .map(|place| (index / 9i128.pow(place)) % 9 - 4)
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = |bound: usize| {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        (state % bound as u64) as usize
    };
    let (mut decided, mut compared) = (0, 0);
    for _ in 0..40 {
        let mut facts = variables
            .iter()
            .flat_map(|v| [(le(&constant(-4), v), true), (le(v, &constant(4)), true)])
            .collect::<Vec<_>>();
        for _ in 0..(1 + next(4)) {
            let (a, b) = (&pool[next(pool.len())], &pool[next(pool.len())]);
            let condition = if next(2) == 0 { lt(a, b) } else { le(a, b) };
            facts.push((condition, next(3) != 0));
        }
        let graph = graph(&facts);
        let mut context = PureFactContext::new();
        for (condition, value) in &facts {
            context = context.assume_condition(condition.clone(), *value);
        }
        let satisfying = models
            .iter()
            .filter(|model| {
                facts
                    .iter()
                    .all(|(fact, value)| holds(fact, model) == *value)
            })
            .collect::<Vec<_>>();
        if satisfying.is_empty() {
            continue;
        }
        assert!(
            !graph.is_contradictory(),
            "satisfiable facts reported contradictory: {facts:?}"
        );
        for a in &pool {
            for b in &pool {
                for query in [lt(a, b), le(a, b)] {
                    let truths = satisfying
                        .iter()
                        .map(|model| holds(&query, model))
                        .collect::<std::collections::BTreeSet<_>>();
                    let entailed = (truths.len() == 1).then(|| truths.contains(&true));
                    let answer = graph.decide(&query);
                    assert!(
                        answer.is_none() || answer == entailed,
                        "{query:?} decided {answer:?} but the models say {entailed:?} under {facts:?}"
                    );
                    assert_eq!(
                        answer, entailed,
                        "{query:?} is entailed but undecided under {facts:?}"
                    );
                    if let (Some(answer), Some(general)) = (answer, context.decide(&query)) {
                        assert_eq!(answer, general, "{query:?} under {facts:?}");
                        compared += 1;
                    }
                    decided += usize::from(answer.is_some());
                }
            }
        }
    }
    assert!(
        decided > 0 && compared > 0,
        "the generated cases should decide something"
    );
}

/// Inserting a fact and answering a question cost the same beside 16 to
/// 1,024 unrelated bounded values: a constant is not a node, so their
/// bounds never join the component the fact or question touches.
#[test]
fn work_is_independent_of_unrelated_bounded_values() {
    let (i, n) = (variable(0), variable(1));
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut graph = DifferenceGraph::new();
        for index in 0..size {
            let other = variable(10 + index);
            graph.assume_condition(&le(&constant(0), &other), true);
            graph.assume_condition(&lt(&other, &constant(4)), true);
        }
        graph.assume_condition(&le(&constant(0), &i), true);
        let (_, insert) = graph_work(|| graph.assume_condition(&lt(&i, &n), true));
        let (answer, query) = graph_work(|| graph.decide(&lt(&i, &constant(4))));
        assert_eq!(answer, None);
        let (answer, path) = graph_work(|| graph.decide(&le(&i, &n)));
        assert_eq!(answer, Some(true));
        samples.push((insert, query, path));
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "graph work should not grow with unrelated values: {samples:?}"
    );
    eprintln!(
        "difference graph (insert, bound query, path query) work at 16/64/256/1024: {samples:?}"
    );
}

/// A fact context's graph follows its facts: what it assumes extends the
/// graph, what it withdraws is gone after the rebuild that withdrawal
/// forces, and a context restricted to some facts answers from those alone.
#[test]
fn a_context_graph_follows_its_facts() {
    let (i, n) = (variable(0), variable(1));
    let below = (lt(&i, &n), true);
    let bounded = (le(&n, &constant(10)), true);
    let context = PureFactContext::new()
        .assume_condition(below.0.clone(), below.1)
        .assume_condition(bounded.0.clone(), bounded.1);
    let query = lt(&i, &constant(10));
    assert_eq!(context.difference_decision(&query, &[]), Some(true));
    // A path's facts not yet in the context are read on top of it.
    let unconstrained = PureFactContext::new().assume_condition(below.0.clone(), below.1);
    assert_eq!(unconstrained.difference_decision(&query, &[]), None);
    assert_eq!(
        unconstrained.difference_decision(&query, std::slice::from_ref(&bounded)),
        Some(true)
    );
    let withdrawn =
        context.without_exact_fact(&crate::kernel::Proposition::ConditionIs(below.0, below.1));
    assert_eq!(withdrawn.difference_decision(&query, &[]), None);
    let restricted = context.restricted_to_facts(&[bounded], &[]);
    assert_eq!(restricted.difference_decision(&query, &[]), None);
    assert_eq!(
        restricted.difference_decision(&le(&n, &constant(10)), &[]),
        Some(true)
    );
}

/// Equating a fresh name to a value names that value's node, so a value
/// with 16 to 256 names is still one node: each equality costs the same,
/// and a bound on the value reaches every name.
#[test]
fn many_names_for_one_value_stay_one_node() {
    let root = variable(0);
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let mut graph = graph(&[
            (le(&constant(0), &root), true),
            (le(&root, &constant(100)), true),
        ]);
        let mut last = 0;
        for index in 0..size {
            let alias = variable(1 + index);
            let ((), work) = graph_work(|| {
                graph.assume_condition(&ConditionTerm::equal(root.clone(), alias.clone()), true);
            });
            last = work;
            assert_eq!(graph.decide(&lt(&alias, &constant(101))), Some(true));
        }
        samples.push(last);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "an equality's work should not grow with the value's other names: {samples:?}"
    );
}

/// Facts about `x + 1`, `x + 2`, ... once `x`'s bounds rule out wrapping
/// are facts about `x`'s node, so a later bound on `x` does not walk one edge
/// pair per offset. Publishing a call's ensures charged two units per such
/// unrelated ambient fact before.
#[test]
fn offsets_of_a_bounded_value_share_its_node() {
    let root = variable(0);
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let mut graph = graph(&[
            (le(&constant(0), &root), true),
            (le(&root, &constant(1000)), true),
        ]);
        for index in 0..size {
            graph.assume_condition(&le(&constant(index), &plus(&root, index)), true);
        }
        let ((), work) = graph_work(|| {
            graph.assume_condition(&lt(&constant(0), &root), true);
        });
        assert_eq!(
            graph.decide(&lt(&constant(size), &plus(&root, size))),
            Some(true)
        );
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "a bound's work should not grow with the value's offsets: {samples:?}"
    );
}

/// Generated facts over three variables whose values sit at the ends of the
/// int32 range and around zero: orders between pool terms and
/// disequalities with constants. Every overflow, division and equality
/// question about compound terms (`x - y`, `0 - x`, `x + 1`, ...) the graph
/// answers holds in every model, with the terms read as wrapping int32
/// arithmetic.
#[test]
fn arithmetic_decisions_hold_in_every_model() {
    use Bitvector32Term as T;
    fn value(term: &Bitvector32Term, variables: &[Bitvector32Term], model: &[i32]) -> i32 {
        match term {
            T::Constant(value) => *value as i32,
            T::Add(a, b) => value(a, variables, model).wrapping_add(value(b, variables, model)),
            T::Subtract(a, b) => {
                value(a, variables, model).wrapping_sub(value(b, variables, model))
            }
            T::Multiply(a, b) => {
                value(a, variables, model).wrapping_mul(value(b, variables, model))
            }
            T::BitwiseXor(a, b) => value(a, variables, model) ^ value(b, variables, model),
            // The pool divides only by constants other than 0 and -1.
            T::Remainder(a, b) => value(a, variables, model) % value(b, variables, model),
            _ => model[variables.iter().position(|v| v == term).unwrap()],
        }
    }
    let values = [i32::MIN, i32::MIN + 1, -1, 0, 1, i32::MAX - 1, i32::MAX];
    let variables = (0..3).map(variable).collect::<Vec<_>>();
    let boxed = |term: &Bitvector32Term| Box::new(term.clone());
    let mut pool = variables.clone();
    pool.push(plus(&variables[0], 1));
    pool.push(T::Subtract(boxed(&variables[1]), boxed(&constant(1))));
    pool.push(T::Subtract(boxed(&constant(0)), boxed(&variables[2])));
    pool.push(T::Subtract(boxed(&variables[0]), boxed(&variables[1])));
    pool.push(T::Add(boxed(&variables[1]), boxed(&variables[2])));
    pool.push(T::Multiply(boxed(&variables[0]), boxed(&constant(2))));
    // C's unsigned order, spelled as a signed one.
    pool.push(T::BitwiseXor(
        boxed(&constant(i32::MIN)),
        boxed(&variables[1]),
    ));
    pool.push(T::BitwiseXor(
        boxed(&variables[2]),
        boxed(&constant(i32::MIN)),
    ));
    pool.push(T::Remainder(boxed(&variables[0]), boxed(&constant(2))));
    pool.push(T::Remainder(boxed(&variables[1]), boxed(&constant(-3))));
    let constants = [i32::MIN, -1, 0, 1, i32::MAX].map(constant);
    let holds = |condition: &ConditionTerm, model: &[i32]| -> bool {
        let v = |term: &Bitvector32Term| value(term, &variables, model);
        match condition {
            ConditionTerm::Constant(value) => *value,
            ConditionTerm::Bitvector32SignedLessThan(a, b) => v(a) < v(b),
            ConditionTerm::Bitvector32SignedLessEqual(a, b) => v(a) <= v(b),
            ConditionTerm::Bitvector32Equal(a, b) => v(a) == v(b),
            ConditionTerm::Bitvector32SignedAddOverflows(a, b) => v(a).overflowing_add(v(b)).1,
            ConditionTerm::Bitvector32SignedSubtractOverflows(a, b) => v(a).overflowing_sub(v(b)).1,
            ConditionTerm::Bitvector32SignedDivideOverflows(a, b) => v(a) == i32::MIN && v(b) == -1,
            ConditionTerm::Bitvector32SignedMultiplyOverflows(a, b) => v(a).overflowing_mul(v(b)).1,
            // As `ConditionTerm::signed_shift_left_overflows` folds
            // constants; the graph answers only counts in `0..32`.
            ConditionTerm::Bitvector32SignedShiftLeftOverflows(a, b) => {
                let count = v(b);
                (0..32).contains(&count)
                    && v(a) >= 0
                    && (i64::from(v(a)) << count) > i64::from(i32::MAX)
            }
            other => unreachable!("{other:?}"),
        }
    };
    let models = (0..values.len().pow(3))
        .map(|index| {
            (0..3)
                .map(|place| values[(index / values.len().pow(place)) % values.len()])
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mut state = 0x2545_f491_4f6c_dd1du64;
    let mut next = |bound: usize| {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        (state % bound as u64) as usize
    };
    let mut decided = 0;
    for _ in 0..200 {
        let mut facts = Vec::new();
        for _ in 0..(1 + next(4)) {
            let a = &pool[next(pool.len())];
            let fact = match next(4) {
                0 => lt(a, &constants[next(constants.len())]),
                1 => le(&constants[next(constants.len())], a),
                2 => ConditionTerm::equal(variables[next(3)].clone(), constants[next(5)].clone()),
                _ => ConditionTerm::Bitvector32SignedAddOverflows(
                    boxed(a),
                    boxed(&pool[next(pool.len())]),
                ),
            };
            facts.push((fact, next(3) != 0));
        }
        let graph = graph(&facts);
        let satisfying = models
            .iter()
            .filter(|model| {
                facts
                    .iter()
                    .all(|(fact, value)| holds(fact, model) == *value)
            })
            .collect::<Vec<_>>();
        if satisfying.is_empty() {
            continue;
        }
        assert!(
            !graph.is_contradictory(),
            "satisfiable facts reported contradictory: {facts:?}"
        );
        let operands = pool.iter().chain(&constants).collect::<Vec<_>>();
        for a in &operands {
            for b in &operands {
                let (a, b) = (boxed(a), boxed(b));
                for query in [
                    ConditionTerm::Bitvector32SignedAddOverflows(a.clone(), b.clone()),
                    ConditionTerm::Bitvector32SignedSubtractOverflows(a.clone(), b.clone()),
                    ConditionTerm::Bitvector32SignedDivideOverflows(a.clone(), b.clone()),
                    ConditionTerm::Bitvector32SignedMultiplyOverflows(a.clone(), b.clone()),
                    ConditionTerm::Bitvector32SignedShiftLeftOverflows(a.clone(), b.clone()),
                    ConditionTerm::Bitvector32Equal(a.clone(), b.clone()),
                    ConditionTerm::Bitvector32SignedLessThan(a.clone(), b.clone()),
                ] {
                    let Some(answer) = graph.decide(&query) else {
                        continue;
                    };
                    decided += 1;
                    assert!(
                        satisfying
                            .iter()
                            .all(|model| holds(&query, model) == answer),
                        "{query:?} decided {answer} but a model disagrees under {facts:?}"
                    );
                }
            }
        }
    }
    assert!(decided > 0, "the generated cases should decide something");
}

/// A disequality at an interval's end moves the end: `x != INT_MIN` rules
/// out `0 - x` and `x / y` overflowing, and `y != -1` rules out the
/// division's.
#[test]
fn a_disequality_at_a_range_end_tightens_it() {
    let (x, y) = (variable(0), variable(1));
    let boxed = |term: &Bitvector32Term| Box::new(term.clone());
    let divide = ConditionTerm::Bitvector32SignedDivideOverflows(boxed(&x), boxed(&y));
    let negate = ConditionTerm::Bitvector32SignedSubtractOverflows(boxed(&constant(0)), boxed(&x));
    assert_eq!(graph(&[]).decide(&divide), None);
    let not_min = graph(&[(ConditionTerm::equal(x.clone(), constant(i32::MIN)), false)]);
    assert_eq!(not_min.decide(&negate), Some(false));
    assert_eq!(not_min.decide(&divide), Some(false));
    let not_minus_one = graph(&[(ConditionTerm::equal(y.clone(), constant(-1)), false)]);
    assert_eq!(not_minus_one.decide(&divide), Some(false));
    assert_eq!(
        not_minus_one.decide(&ConditionTerm::equal(y.clone(), constant(-1))),
        Some(false)
    );
    // An exclusion recorded inside the interval takes effect once a bound
    // reaches it.
    let later = graph(&[
        (ConditionTerm::equal(x.clone(), constant(3)), false),
        (le(&constant(3), &x), true),
    ]);
    assert_eq!(later.decide(&lt(&constant(3), &x)), Some(true));
    let pinned = graph(&[
        (le(&constant(3), &x), true),
        (le(&x, &constant(3)), true),
        (ConditionTerm::equal(x.clone(), constant(3)), false),
    ]);
    assert!(pinned.is_contradictory());
    // A dead path answers only that an overflow is absent.
    assert_eq!(pinned.decide(&divide), Some(false));
    assert_eq!(pinned.decide(&lt(&x, &y)), None);
}

/// A compound term a fact mentions gets a node of its own; its operands'
/// bounds still bound it. Here `y - x` is named by `0 <= (y - x) - 1`
/// before the question, and `x < y`, `0 <= x` keep `(y - x) - 1` from
/// overflowing.
#[test]
fn a_named_compound_term_keeps_its_operands_bounds() {
    let (x, y) = (variable(0), variable(1));
    let boxed = |term: &Bitvector32Term| Box::new(term.clone());
    let difference = Bitvector32Term::Subtract(boxed(&y), boxed(&x));
    let less_one = Bitvector32Term::Subtract(boxed(&difference), boxed(&constant(1)));
    let graph = graph(&[
        (le(&constant(0), &less_one), true),
        (lt(&x, &y), true),
        (le(&constant(0), &x), true),
    ]);
    assert_eq!(
        graph.decide(&ConditionTerm::Bitvector32SignedSubtractOverflows(
            boxed(&difference),
            boxed(&constant(1))
        )),
        Some(false)
    );
}

/// A recorded `!(a + b overflows)` answers `b + a`, and the same sum under
/// another name for an operand; a shift by a constant count and a product
/// by a constant are bounded by their operand.
#[test]
fn overflow_facts_shifts_and_products_are_read() {
    let (x, y) = (variable(0), variable(1));
    let boxed = |term: &Bitvector32Term| Box::new(term.clone());
    let recorded = graph(&[(
        ConditionTerm::Bitvector32SignedAddOverflows(boxed(&x), boxed(&y)),
        false,
    )]);
    assert_eq!(
        recorded.decide(&ConditionTerm::Bitvector32SignedAddOverflows(
            boxed(&y),
            boxed(&x)
        )),
        Some(false)
    );
    let alias = variable(2);
    let renamed = graph(&[
        (
            ConditionTerm::Bitvector32SignedAddOverflows(boxed(&x), boxed(&y)),
            false,
        ),
        (ConditionTerm::equal(alias.clone(), x.clone()), true),
    ]);
    assert_eq!(
        renamed.decide(&ConditionTerm::Bitvector32SignedAddOverflows(
            boxed(&alias),
            boxed(&y)
        )),
        Some(false)
    );
    let byte = graph(&[(le(&constant(0), &x), true), (le(&x, &constant(255)), true)]);
    assert_eq!(
        byte.decide(&ConditionTerm::Bitvector32SignedShiftLeftOverflows(
            boxed(&x),
            boxed(&constant(1))
        )),
        Some(false)
    );
    let doubled = Bitvector32Term::Multiply(boxed(&x), boxed(&constant(2)));
    assert_eq!(
        byte.decide(&ConditionTerm::Bitvector32SignedSubtractOverflows(
            boxed(&doubled),
            boxed(&constant(1))
        )),
        Some(false)
    );
}

/// C's unsigned `a < b` reaches the kernel as `(a ^ MIN) < (b ^ MIN)`. With
/// `0 <= b <= 4`, `b ^ MIN` is `b + MIN`, so `a ^ MIN < MIN + 4` is
/// negative, which makes `a` non-negative and `a ^ MIN` equal `a + MIN`:
/// `0 <= a <= 3`.
#[test]
fn an_unsigned_order_spelled_with_a_sign_flip_bounds_both_sides() {
    let (a, b) = (variable(0), variable(1));
    let boxed = |term: &Bitvector32Term| Box::new(term.clone());
    let flip = |term: &Bitvector32Term| {
        Bitvector32Term::BitwiseXor(boxed(&constant(i32::MIN)), boxed(term))
    };
    let graph = graph(&[
        (lt(&flip(&a), &flip(&b)), true),
        (le(&constant(0), &b), true),
        (le(&b, &constant(4)), true),
    ]);
    assert_eq!(graph.decide(&le(&constant(0), &a)), Some(true));
    assert_eq!(graph.decide(&le(&a, &constant(3))), Some(true));
    assert_eq!(graph.decide(&lt(&a, &b)), Some(true));
}

/// A remainder by a constant is bounded by its dividend's sign and the
/// divisor, and a side with no node of its own is compared by interval:
/// `x == 0` gives `x % 2 == 0`, and `0 <= x` gives `x % 4 < 4`.
#[test]
fn a_remainder_by_a_constant_is_bounded() {
    let x = variable(0);
    let boxed = |term: &Bitvector32Term| Box::new(term.clone());
    let remainder = |k: i32| Bitvector32Term::Remainder(boxed(&x), boxed(&constant(k)));
    let zero = graph(&[(ConditionTerm::equal(x.clone(), constant(0)), true)]);
    assert_eq!(
        zero.decide(&ConditionTerm::equal(remainder(2), constant(0))),
        Some(true)
    );
    let nonnegative = graph(&[(le(&constant(0), &x), true)]);
    assert_eq!(
        nonnegative.decide(&lt(&remainder(4), &constant(4))),
        Some(true)
    );
    assert_eq!(
        nonnegative.decide(&le(&constant(0), &remainder(4))),
        Some(true)
    );
    // `x % 4` can be 3: the bound is exact.
    assert_eq!(nonnegative.decide(&le(&remainder(4), &constant(2))), None);
    assert_eq!(
        graph(&[]).decide(&lt(&remainder(4), &constant(4))),
        Some(true)
    );
    assert_eq!(graph(&[]).decide(&le(&constant(0), &remainder(4))), None);
}

/// The `int64` division guard also holds for a zero divisor (its
/// constructor folds `right == 0` to overflow), so a divisor known only to
/// be non-negative leaves it open; the `int32` guard leaves zero to a
/// separate check and is answered.
#[test]
fn an_int64_division_guard_needs_a_nonzero_divisor() {
    let (n, d) = (variable(0), variable(1));
    let int64 = Bitvector32Term::Int64Constant;
    let nonnegative = graph(&[(
        ConditionTerm::int64_signed_less_equal(int64(0), d.clone()),
        true,
    )]);
    let divide =
        ConditionTerm::Bitvector64SignedDivideOverflows(Box::new(n.clone()), Box::new(d.clone()));
    assert_eq!(nonnegative.decide(&divide), None);
    let zero = graph(&[(ConditionTerm::int64_equal(d.clone(), int64(0)), true)]);
    assert_eq!(zero.decide(&divide), None);
    let positive = graph(&[(
        ConditionTerm::int64_signed_less_than(int64(0), d.clone()),
        true,
    )]);
    assert_eq!(positive.decide(&divide), Some(false));
    let nonzero = graph(&[
        (
            ConditionTerm::int64_signed_less_equal(int64(0), d.clone()),
            true,
        ),
        (ConditionTerm::int64_equal(d.clone(), int64(0)), false),
    ]);
    assert_eq!(nonzero.decide(&divide), Some(false));
    let int32 = graph(&[(le(&constant(0), &d), true)]);
    assert_eq!(
        int32.decide(&ConditionTerm::Bitvector32SignedDivideOverflows(
            Box::new(n),
            Box::new(d)
        )),
        Some(false)
    );
}
/// A value many others are bounded by (an array length `n` with
/// `v_i <= n` for 64 to 4,096 values) is a hub: a new bound on it, a
/// question about it, and a question about one dependent cost the same at
/// every size. Insertion pushes a bound a bounded distance and a query
/// pulls one bounded hop, so a dependent still reads its hub's bound.
#[test]
fn a_bound_on_a_shared_value_costs_the_same_beside_any_number_of_dependents() {
    let n = variable(0);
    let mut samples = Vec::new();
    for size in [64, 256, 1024, 4096] {
        let mut graph = DifferenceGraph::new();
        for index in 0..size {
            graph.assume_condition(&le(&variable(10 + index), &n), true);
        }
        let (_, insert) = graph_work(|| graph.assume_condition(&le(&n, &constant(10)), true));
        let first = variable(10);
        let (answer, dependent) = graph_work(|| graph.decide(&le(&first, &constant(10))));
        assert_eq!(answer, Some(true));
        let (answer, hub) = graph_work(|| graph.decide(&le(&n, &constant(10))));
        assert_eq!(answer, Some(true));
        let (_, joined) = graph_work(|| graph.assume_condition(&lt(&variable(5), &n), true));
        samples.push((insert, dependent, hub, joined));
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "work on a shared value should not grow with its dependents: {samples:?}"
    );
}

/// A fact names a load by its load variable, the load's canonical form; a
/// question may spell the load itself. The context's graph is asked the
/// canonical question too, so `0 <= v` answers `0 <= load` for the load `v`
/// names.
#[test]
fn a_load_spelled_as_itself_reads_facts_about_its_load_variable() {
    let pointer = crate::kernel::Pointer {
        block: "difference-graph-cell".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let memory = crate::kernel::CMemory::new().with_block("difference-graph-cell", 4);
    let load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory),
        Box::new(pointer),
        crate::kernel::LoadKind::Bits32,
    );
    let named = crate::kernel::eval::canonical_term(&load);
    assert_ne!(named, load, "the load takes a load variable");
    let context = PureFactContext::new().assume_condition(le(&constant(0), &named), true);
    assert_eq!(
        context.difference_decision(&le(&constant(0), &load), &[]),
        Some(true)
    );
    assert_eq!(
        context.difference_decision(&lt(&load, &constant(0)), &[]),
        Some(false)
    );
}

/// Pointer offsets of `int32` elements compare as their indices: equal
/// widths compare values, a constant byte offset compares the value with
/// its element count, and a byte offset no whole number of elements
/// reaches is never equal.
#[test]
fn pointer_offsets_of_int32_elements_compare_as_indices() {
    use crate::kernel::PointerOffsetTerm as O;
    let (i, j) = (variable(0), variable(1));
    let scaled = |value: &Bitvector32Term| O::Int32Scaled {
        value: Box::new(value.clone()),
        byte_width: 4,
    };
    let offsets_equal = |a: O, b: O| ConditionTerm::PointerOffsetEqual(Box::new(a), Box::new(b));
    let ordered = graph(&[(lt(&i, &j), true)]);
    assert_eq!(
        ordered.decide(&offsets_equal(scaled(&i), scaled(&j))),
        Some(false)
    );
    let pinned = graph(&[(ConditionTerm::equal(i.clone(), constant(3)), true)]);
    assert_eq!(
        pinned.decide(&offsets_equal(scaled(&i), O::Constant(12))),
        Some(true)
    );
    assert_eq!(
        pinned.decide(&offsets_equal(O::Constant(16), scaled(&i))),
        Some(false)
    );
    assert_eq!(
        graph(&[]).decide(&offsets_equal(scaled(&i), O::Constant(6))),
        Some(false)
    );
    assert_eq!(
        graph(&[]).decide(&offsets_equal(scaled(&i), scaled(&j))),
        None
    );
    // A recorded offset equality is an index equality.
    let recorded = graph(&[
        (offsets_equal(scaled(&i), scaled(&j)), true),
        (le(&j, &constant(5)), true),
    ]);
    assert_eq!(recorded.decide(&le(&i, &constant(5))), Some(true));
}
