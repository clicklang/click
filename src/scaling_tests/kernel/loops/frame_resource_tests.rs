// Scaling coverage for rebuilding a loop's retained frame in kernel/loops.rs.
use super::*;

#[test]
fn a_loop_frame_normalizes_its_retained_views_once() {
    let mut samples = Vec::new();
    for count in [4u64, 8, 16, 32, 64] {
        let assumptions = PureFactContext::new();
        let state = CState::new();
        let views = (0..count)
            .map(|index| {
                CResourceFact::view_memory(CMemoryRange::new(
                    Pointer::symbolic(Variable(9_360_000 + index)),
                    Bitvector32Term::Constant(0),
                    Bitvector32Term::Constant(1),
                ))
            })
            .collect::<Vec<_>>();
        let withheld = views
            .iter()
            .cloned()
            .fold(ResourceContext::new(), |resources, fact| {
                resources.unchecked_with_fact(fact)
            });
        let (body, work) = crate::instrumentation::measure_deterministic_work(|| {
            with_loop_frame_resources(
                ResourceContext::new(),
                &withheld,
                true,
                &state,
                &assumptions,
            )
        });
        assert_eq!(body.facts().len(), views.len());
        for view in &views {
            assert!(body.contains_exact_representation(view));
        }
        let hidden = with_loop_frame_resources(
            ResourceContext::new(),
            &withheld,
            false,
            &state,
            &assumptions,
        );
        assert!(
            hidden.facts().is_empty(),
            "an explicit view interface hides undeclared frame views"
        );
        samples.push((count, work));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1.saturating_mul(3) + 64, "{samples:?}");
    }
}
