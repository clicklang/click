//! The fixture harnesses' verifier threads.
//!
//! A gate verdict comes from deterministic work budgets, the per-class
//! tactic budgets that every library verification entry point installs; no
//! verifier limit is a wall clock, so machine load cannot turn a passing
//! fixture red, and a harness needs no special scope to get that. nextest's
//! per-test timeout remains the process-level hang containment.
//!
//! What harnesses share here is how they start verifier threads: [`spawn`]
//! gives each one the 64 MiB stack deep proofs need, and [`run_parallel`]
//! fans fixtures out over the cores the same way. `tests/documentation.rs`
//! checks that no harness installs a wall-clock bound of its own; see
//! `docs/internals/testing.md` for how to add a harness.

#![allow(dead_code, reason = "each harness uses only the helpers it needs")]

/// Runs `operation` on a named verifier thread with a 64 MiB stack and
/// waits for it. `label` names the thread's role in the start and panic
/// errors.
pub fn spawn<R: Send + 'static>(
    label: &str,
    name: String,
    operation: impl FnOnce() -> R + Send + 'static,
) -> Result<R, String> {
    std::thread::Builder::new()
        .name(name)
        .stack_size(64 * 1024 * 1024)
        .spawn(operation)
        .map_err(|error| format!("failed to start {label}: {error}"))?
        .join()
        .map_err(|_| format!("{label} panicked"))
}

/// [`click::cli::run_parallel`], the harnesses' one way to verify fixtures
/// on every core.
pub fn run_parallel<T, F>(items: &[T], workers: usize, run: F) -> Vec<(usize, String)>
where
    T: Sync,
    F: Fn(&T) -> Result<(), String> + Sync,
{
    click::cli::run_parallel(items, workers, run)
}
