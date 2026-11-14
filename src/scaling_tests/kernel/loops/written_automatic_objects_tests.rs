// Scaling tests of `src/kernel/loops.rs` (module `written_automatic_objects_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

fn object_slot(name: &str) -> Pointer {
    Pointer {
        block: PointerBlock::Concrete(format!("local:{name}")),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    }
}

/// A loop body that hands a local struct to a call writes it, so the loop's
/// write set holds that struct, and finding it costs the body's expressions,
/// not the frame's other automatic objects.
#[test]
fn loop_written_objects_scale_with_the_body_not_the_frame() {
    fn work(body_calls: usize, unrelated: usize) -> usize {
        let _session = crate::kernel::VerificationSession::enter();
        let mut state = ExecutionState::new();
        let layout = AggregateLayout::holding_value(ProgramType::Int32);
        state
            .locals
            .set_aggregate_object_at("c", layout.clone(), object_slot("c"));
        for index in 0..unrelated {
            let name = format!("unrelated_{index}");
            state
                .locals
                .set_aggregate_object_at(name.clone(), layout.clone(), object_slot(&name));
        }
        let mut body = ProgramStatement::Skip;
        for _ in 0..body_calls {
            body = c_seq(body, c_call("bump", vec![c_variable("c")]));
        }
        let (ranges, work) = crate::instrumentation::measure_deterministic_work(|| {
            loop_written_automatic_objects(&state, &body, &BTreeSet::new())
        });
        assert_eq!(ranges.len(), 1);
        assert_eq!(ranges[0].base(), &object_slot("c"));
        work
    }
    let unrelated = [0, 8, 64, 256].map(|size| work(4, size));
    assert!(unrelated[0] > 0);
    assert!(
        unrelated.iter().all(|cost| *cost == unrelated[0]),
        "{unrelated:?}"
    );
    let bodies = [4, 8, 16, 32].map(|size| work(size, 0));
    assert!(
        bodies.windows(2).all(|pair| pair[1] <= 3 * pair[0]),
        "{bodies:?}"
    );
}
