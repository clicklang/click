// Deterministic work for pointer-valued pure-call congruence.
use super::*;

#[test]
fn nested_pointer_call_registration_and_late_merges_scale_with_selected_dag() {
    let _session = VerificationSession::enter();
    let samples = [16, 64, 256, 1024].map(|depth| {
        let build = |mut p| {
            for _ in 0..depth {
                p = call("next", vec![pointer_argument(p)]);
            }
            p
        };
        let p = Pointer::symbolic(Variable(100));
        let q = Pointer::symbolic(Variable(101));
        let (a, b) = (build(p.clone()), build(q.clone()));
        let (((), work), maps) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let mut graph = EqualityGraph::default();
                assert!(!graph.are_equal(&a, &b));
                equal_pointer_arguments(&mut graph, &p, &q);
                assert!(graph.are_equal(&a, &b));
            })
        });
        (work, maps)
    });
    assert!(
        samples
            .windows(2)
            .all(|p| p[1].0 <= p[0].0 * 5 && p[1].1 <= p[0].1 * 6),
        "{samples:?}"
    );
}

#[test]
fn pointer_call_queries_do_not_scan_unrelated_facts() {
    let _session = VerificationSession::enter();
    let samples = [16, 64, 256, 1024].map(|size| {
        let mut graph = EqualityGraph::default();
        for id in 0..size {
            graph.add_int32_equality(&word(1000 + 2 * id), &word(1001 + 2 * id));
        }
        let (p, q) = (
            Pointer::symbolic(Variable(100)),
            Pointer::symbolic(Variable(101)),
        );
        equal_pointer_arguments(&mut graph, &p, &q);
        crate::instrumentation::measure_deterministic_work(|| {
            assert!(graph.are_equal(
                &call("select", vec![pointer_argument(p)]),
                &call("select", vec![pointer_argument(q)])
            ));
        })
        .1
    });
    assert!(samples.windows(2).all(|p| p[1] <= p[0] * 2), "{samples:?}");
}
