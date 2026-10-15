// Scaling tests of `src/kernel/difference_graph/tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

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

/// Written bounds must remain available beyond the graph walk's edge cap.
/// Both directions and strictness use only the selected edge, not its hub.
#[test]
#[ignore = "nightly: 1.4s multi-domain high-degree bound scaling"]
fn written_order_queries_are_flat_beside_a_high_degree_bound() {
    let order = |domain, strict, left: &Bitvector32Term, right: &Bitvector32Term| {
        let (left, right) = (Box::new(left.clone()), Box::new(right.clone()));
        match (domain, strict) {
            (Domain::Int32, true) => ConditionTerm::Bitvector32SignedLessThan(left, right),
            (Domain::Int32, false) => ConditionTerm::Bitvector32SignedLessEqual(left, right),
            (Domain::Int64, true) => ConditionTerm::Bitvector64SignedLessThan(left, right),
            (Domain::Int64, false) => ConditionTerm::Bitvector64SignedLessEqual(left, right),
            (Domain::UInt64, true) => ConditionTerm::Bitvector64UnsignedLessThan(left, right),
            (Domain::UInt64, false) => ConditionTerm::Bitvector64UnsignedLessEqual(left, right),
        }
    };
    for domain in [Domain::Int32, Domain::Int64, Domain::UInt64] {
        for strict in [false, true] {
            let mut samples = Vec::new();
            for size in [16, 33, 64, 256, 1024] {
                let length = variable(0);
                let mut graph = DifferenceGraph::new();
                for index in 0..size {
                    graph.assume_condition(
                        &order(domain, strict, &variable(1 + index), &length),
                        true,
                    );
                }
                let mut work = Vec::new();
                for index in [0, size / 2, size - 1] {
                    let index = variable(1 + index);
                    let (answer, cost) =
                        graph_work(|| graph.decide(&order(domain, strict, &index, &length)));
                    assert_eq!(answer, Some(true), "{domain:?}, {strict}, {size}");
                    work.push(cost);
                    let (answer, cost) =
                        graph_work(|| graph.decide(&order(domain, !strict, &length, &index)));
                    assert_eq!(answer, Some(false), "{domain:?}, {strict}, {size}");
                    work.push(cost);
                    if !strict {
                        assert_eq!(
                            graph.decide(&order(domain, true, &index, &length)),
                            None,
                            "a non-strict premise cannot establish a strict bound"
                        );
                    }
                }
                samples.push(work);
            }
            assert!(
                samples.windows(2).all(|pair| pair[0] == pair[1]),
                "{domain:?}, {strict}: {samples:?}"
            );
        }
    }
}
