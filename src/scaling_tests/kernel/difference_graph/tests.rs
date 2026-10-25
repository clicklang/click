// Scaling tests of `src/kernel/difference_graph/tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

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

/// A `uint32` order's nodes are paired with their words' `Int32` nodes, so
/// beside 64 to 512 values with unsigned bounds of their own and signed
/// bounds by a shared hub, an unsigned fact, an unsigned question, and a
/// signed question the pairing answers cost the same: the pairing links one
/// word's two nodes and nothing else, and a bound on the hub follows at most
/// `EDGE_LIMIT` of its edges.
#[test]
fn unsigned_work_is_flat_beside_values_bounded_by_its_hub() {
    let (i, n) = (variable(0), variable(1));
    let unsigned_lt = |a: &Bitvector32Term, b: &Bitvector32Term| {
        ConditionTerm::unsigned_less_than(a.clone(), b.clone())
    };
    let mut samples = Vec::new();
    for size in [64, 128, 512] {
        let mut graph = DifferenceGraph::new();
        for index in 0..size {
            let other = variable(10 + index);
            graph.assume_condition(&unsigned_lt(&other, &constant(4)), true);
            graph.assume_condition(&lt(&other, &n), true);
        }
        graph.assume_condition(&unsigned_lt(&n, &constant(1000)), true);
        let (_, insert) = graph_work(|| graph.assume_condition(&unsigned_lt(&i, &n), true));
        let (answer, unsigned) = graph_work(|| graph.decide(&unsigned_lt(&i, &constant(1000))));
        assert_eq!(answer, Some(true));
        let (answer, signed) = graph_work(|| graph.decide(&le(&constant(0), &i)));
        assert_eq!(answer, Some(true));
        samples.push((insert, unsigned, signed));
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "unsigned graph work should not grow with unrelated values: {samples:?}"
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
        ConditionTerm::Compare {
            format: match domain {
                Domain::Int32 => MachineIntegerType::Int32,
                Domain::Int64 => MachineIntegerType::Int64,
                Domain::UInt64 => MachineIntegerType::UInt64,
                Domain::UInt32 => MachineIntegerType::UInt32,
            },
            relation: if strict {
                CompareRelation::LessThan
            } else {
                CompareRelation::LessEqual
            },
            left,
            right,
        }
    };
    for domain in [Domain::Int32, Domain::Int64, Domain::UInt64, Domain::UInt32] {
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

/// A 32-bit order of σ(x), the sign cast, reads `x`'s nodes (rule K1):
/// beside 16 to 1,024 unrelated bounded values it decides what the same
/// order of `x` decides, at the same work, so the read-through adds no
/// node and no search.
#[test]
fn an_order_of_a_sign_cast_costs_what_the_order_of_its_word_costs() {
    let (i, n) = (variable(0), variable(1));
    let cast = |source, destination| Bitvector32Term::sign_cast32(source, destination, i.clone());
    let order = |format, left: Bitvector32Term| ConditionTerm::Compare {
        format,
        relation: CompareRelation::LessEqual,
        left: Box::new(left),
        right: Box::new(n.clone()),
    };
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut graph = DifferenceGraph::new();
        for index in 0..size {
            let other = variable(10 + index);
            graph.assume_condition(&le(&constant(0), &other), true);
            graph.assume_condition(&lt(&other, &constant(4)), true);
        }
        graph.assume_condition(&le(&constant(0), &i), true);
        graph.assume_condition(&lt(&i, &n), true);
        let mut work = Vec::new();
        for (format, source, destination) in [
            (
                MachineIntegerType::Int32,
                MachineIntegerType::UInt32,
                MachineIntegerType::Int32,
            ),
            (
                MachineIntegerType::UInt32,
                MachineIntegerType::Int32,
                MachineIntegerType::UInt32,
            ),
        ] {
            let (plain, plain_work) = graph_work(|| graph.decide(&order(format, i.clone())));
            let (cast, cast_work) =
                graph_work(|| graph.decide(&order(format, cast(source, destination))));
            assert_eq!(plain, Some(true), "{format:?}, {size}");
            assert_eq!(cast, plain, "{format:?}, {size}");
            assert_eq!(cast_work, plain_work, "{format:?}, {size}");
            work.push(cast_work);
        }
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "work should not grow with unrelated values: {samples:?}"
    );
}
