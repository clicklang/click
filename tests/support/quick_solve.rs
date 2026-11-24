use click::instrumentation;
use click::surface::{ClickError, ClickErrorKind};

const QUICK_SOLVE_WORK_LIMIT: usize = 50_000;

pub fn check_quick_solve(
    samples: &[instrumentation::TacticWorkSample],
    result: &Result<(), ClickError>,
) -> Result<(), String> {
    let work_limit = std::env::var_os("CLICK_DISABLE_TACTIC_BUDGETS")
        .is_none()
        .then_some(QUICK_SOLVE_WORK_LIMIT);
    check_quick_solve_with_limit(samples, result, work_limit)
}

pub fn check_quick_solve_with_limit(
    samples: &[instrumentation::TacticWorkSample],
    result: &Result<(), ClickError>,
    work_limit: Option<usize>,
) -> Result<(), String> {
    if let Err(error) = result
        && (error.verification_stopped() || error.kind() == ClickErrorKind::Internal)
    {
        return Err(format!(
            "Quick Solve Test did not finish: {}",
            error.report()
        ));
    }
    // Program closing profiles its generated termination proof as a solve
    // even when the fixture has no written solve at that source.
    let mut solves = samples.iter().filter(|sample| {
        sample.tactic.claim != "program.termination"
            && matches!(
                (
                    sample.tactic.tactic_name.as_str(),
                    sample.tactic.class.as_str()
                ),
                ("solve" | "close", "smart")
            )
    });
    let Some(solve) = solves.next() else {
        return Err("Quick Solve Test must reach one explicit `solve()` or `close() using`".into());
    };
    if solves.next().is_some() {
        return Err(
            "Quick Solve Test ran more than one explicit `solve()` or `close() using`".into(),
        );
    }
    let work = solve.inclusive_work;
    if let Some(limit) = work_limit
        && work > limit
    {
        return Err(format!(
            "Quick Solve Test used {work} deterministic work units (limit {limit}) in `{}`",
            solve.tactic.claim
        ));
    }
    Ok(())
}
