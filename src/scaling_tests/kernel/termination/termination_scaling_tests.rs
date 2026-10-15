// Scaling tests of `src/kernel/termination.rs` (module `termination_scaling_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// The deepest graph: height equals the node count, so every level holds
/// one function and the check settles `n` levels in ascending order.
#[test]
fn one_long_call_chain_costs_linear_termination_work() {
    let name = |index: usize| format!("chain{index:06}");
    let mut samples = Vec::new();
    for size in SIZES {
        let rules = (0..size)
            .map(|index| {
                let callees = if index + 1 < size {
                    vec![name(index + 1)]
                } else {
                    Vec::new()
                };
                rule(&name(index), &callees)
            })
            .collect::<Vec<_>>();
        samples.push(sample(size, &rules, |heights, verdicts| {
            assert_eq!(heights[&name(0)], size - 1);
            assert_eq!(heights[&name(size - 1)], 0);
            assert_eq!(verdicts.rules.len(), size, "a call chain all terminates");
            assert!(verdicts.refusals.is_empty());
        }));
    }
    report("call chain", &samples);
    assert_near_linear("call chain", &samples);
}

/// The widest graph: one level of `n` leaves, and a root whose own call
/// list is the whole edge set.
#[test]
fn wide_fan_out_costs_linear_termination_work() {
    let leaf = |index: usize| format!("leaf{index:06}");
    let mut samples = Vec::new();
    for size in SIZES {
        let leaves = (0..size).map(leaf).collect::<Vec<_>>();
        let mut rules = vec![rule("root", &leaves)];
        rules.extend(leaves.iter().map(|name| rule(name, &[])));
        samples.push(sample(size, &rules, |heights, verdicts| {
            assert_eq!(heights["root"], 1);
            assert_eq!(heights[&leaf(0)], 0);
            assert_eq!(
                verdicts.rules.len(),
                size + 1,
                "a root over terminating leaves terminates"
            );
            assert!(verdicts.refusals.is_empty());
        }));
    }
    report("wide fan-out", &samples);
    assert_near_linear("wide fan-out", &samples);
}

/// Many two-member cycles, each with its own caller. Every cycle member is
/// refused for unmeasured recursion, every refusal is pushed through the
/// level worklist, and every caller then reads a refused callee.
#[test]
fn many_small_unmeasured_cycles_cost_linear_termination_work() {
    let ping = |index: usize| format!("ping{index:06}");
    let pong = |index: usize| format!("pong{index:06}");
    let caller = |index: usize| format!("caller{index:06}");
    let mut samples = Vec::new();
    for size in SIZES {
        let groups = size / 2;
        let mut rules = Vec::new();
        for index in 0..groups {
            rules.push(rule(&ping(index), &[pong(index)]));
            rules.push(rule(&pong(index), &[ping(index)]));
            rules.push(rule(&caller(index), &[ping(index)]));
        }
        samples.push(sample(size, &rules, |heights, verdicts| {
            assert_eq!(heights[&ping(0)], 0, "a cycle's members share a height");
            assert_eq!(heights[&pong(0)], 0);
            assert_eq!(heights[&caller(0)], 1);
            assert!(verdicts.rules.is_empty(), "nothing here terminates");
            for index in [0, groups - 1] {
                assert!(matches!(
                    verdicts.refusals[&ping(index)],
                    CTerminationRefusal::UnmeasuredRecursion { .. }
                ));
                assert!(matches!(
                    verdicts.refusals[&pong(index)],
                    CTerminationRefusal::UnmeasuredRecursion { .. }
                ));
                assert_eq!(
                    verdicts.refusals[&caller(index)],
                    CTerminationRefusal::Callee {
                        callee: ping(index)
                    }
                );
            }
        }));
    }
    report("many small unmeasured cycles", &samples);
    assert_near_linear("many small unmeasured cycles", &samples);
}

/// One strongly connected component of `n` functions: the planner's
/// explicit stack holds every member at once, and the check settles them
/// as a single level.
#[test]
fn one_large_cycle_costs_linear_termination_work() {
    let name = |index: usize| format!("ring{index:06}");
    let mut samples = Vec::new();
    for size in SIZES {
        let rules = (0..size)
            .map(|index| rule(&name(index), &[name((index + 1) % size)]))
            .collect::<Vec<_>>();
        samples.push(sample(size, &rules, |heights, verdicts| {
            assert!(
                (0..size).all(|index| heights[&name(index)] == 0),
                "one cycle is one level"
            );
            assert!(verdicts.rules.is_empty());
            assert!(
                (0..size).all(|index| matches!(
                    verdicts.refusals[&name(index)],
                    CTerminationRefusal::UnmeasuredRecursion { .. }
                )),
                "every member of an unmeasured cycle is refused for it"
            );
        }));
    }
    report("one large cycle", &samples);
    assert_near_linear("one large cycle", &samples);
}

/// A layered DAG whose edges outnumber its nodes four to one, so a check
/// linear in edges and one linear only in nodes are distinguishable.
#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn a_layered_dag_costs_linear_termination_work() {
    const WIDTH: usize = 8;
    const FAN_OUT: usize = 4;
    let name = |layer: usize, index: usize| format!("dag{layer:06}_{index}");
    let mut samples = Vec::new();
    for size in SIZES {
        let layers = size.div_ceil(WIDTH);
        let nodes = layers * WIDTH;
        let mut rules = Vec::new();
        for layer in 0..layers {
            for index in 0..WIDTH {
                let callees = if layer + 1 < layers {
                    (0..FAN_OUT)
                        .map(|step| name(layer + 1, (index + step) % WIDTH))
                        .collect::<Vec<_>>()
                } else {
                    Vec::new()
                };
                rules.push(rule(&name(layer, index), &callees));
            }
        }
        assert_eq!(rules.len(), nodes);
        samples.push(sample(size, &rules, |heights, verdicts| {
            assert_eq!(heights[&name(0, 0)], layers - 1, "the top layer is deepest");
            assert_eq!(heights[&name(layers - 1, 0)], 0);
            assert_eq!(verdicts.rules.len(), nodes, "a DAG all terminates");
            assert!(verdicts.refusals.is_empty());
        }));
    }
    report("layered DAG", &samples);
    assert_near_linear("layered DAG", &samples);
}
