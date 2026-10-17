// Scaling tests of `src/kernel/proof/execution.rs` (module `checked_callee_dependency_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// Reusing a wide summary must visit its syntax once, rather than once
/// per occurrence. Both the call count and reuse count grow here.
#[test]
fn checked_callee_summary_reuse_scales_with_input_not_product() {
    let mut previous = None;
    for size in [16, 64, 256, 1024] {
        let mut body = CStatement::Skip;
        for index in 0..size {
            body = CStatement::seq(
                Arc::new(body),
                Arc::new(crate::kernel::c_call(format!("callee_{index}"), vec![])),
            );
        }
        let summary = crate::kernel::c_while(crate::kernel::c_int32_literal(1), vec![], body);
        let events = (0..size)
            .map(|_| {
                CheckedExecutionEvent::Statement(Theorem::new(Proposition::CStatementVerifies {
                    state: Box::new(CState::new()),
                    statement: Box::new(summary.clone()),
                    outcome: CStatementOutcome::Normal(Box::new(CState::new())),
                }))
            })
            .collect::<Vec<_>>();
        let (calls, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut calls = std::collections::BTreeSet::new();
            collect_checked_callees(&events, &mut Default::default(), &mut calls);
            calls
        });
        eprintln!("summary reuse size={size}, dependency work={work}");
        assert_eq!(calls.len(), size);
        assert!(calls.contains(&format!("callee_{}", size - 1)));
        if let Some(before) = previous {
            assert!(
                work <= 5 * before,
                "superlinear summary reuse: {before} -> {work}"
            );
        }
        previous = Some(work);
    }
}
