//! Cold-check policy belongs to the selected source proof, not every proof
//! the targeted verifier visits while constructing its function environment.
use std::cell::{Cell, RefCell};
use std::rc::Rc;
use std::time::{Duration, Instant};

use crate::instrumentation::{ReplayDiscovery, ReplayDiscoveryScope};

struct Selection {
    label: String,
    visited: Cell<bool>,
    strict: bool,
    checked_only: bool,
    replay: Option<ReplayMeasurement>,
}

#[derive(Default)]
struct ReplayMeasurement {
    discovery: ReplayDiscovery,
    elapsed: Cell<Duration>,
}

thread_local! {
    static SELECTION: RefCell<Option<Rc<Selection>>> = const { RefCell::new(None) };
    static CHECKED_ONLY: Cell<bool> = const { Cell::new(false) };
    static STRICT_CLAIM: Cell<bool> = const { Cell::new(false) };
}

pub(super) fn selected_claim_is_strict() -> bool {
    CHECKED_ONLY.with(Cell::get) || STRICT_CLAIM.with(Cell::get)
}

/// True inside replay that refuses explicit search as well as implicit solving.
pub(super) fn checked_only() -> bool {
    CHECKED_ONLY.with(Cell::get)
}

struct CheckedOnlyScope(bool);

impl CheckedOnlyScope {
    fn enter(checked_only: bool) -> Self {
        Self(CHECKED_ONLY.with(|active| active.replace(active.get() || checked_only)))
    }
}

impl Drop for CheckedOnlyScope {
    fn drop(&mut self) {
        CHECKED_ONLY.with(|active| active.set(self.0));
    }
}

/// Verify all proofs visited by an operation with proof search disabled.
pub fn without_proof_search<R>(operation: impl FnOnce() -> Result<R, String>) -> Result<R, String> {
    let _policy = CheckedOnlyScope::enter(true);
    let discovery = ReplayDiscovery::default();
    let _discovery = ReplayDiscoveryScope::enter(&discovery);
    let result = operation();
    match discovery.borrow_mut().take() {
        Some(operation) => Err(format!(
            "checked-only verification {operation}; write the selected evidence explicitly"
        )),
        None => result,
    }
}

/// Replay one selected claim and its nested proofs with search disabled.
pub fn without_proof_search_for_claim<R>(
    claim_label: &str,
    operation: impl FnOnce() -> Result<R, String>,
) -> Result<R, String> {
    check_selected_claim(claim_label, true, true, true, operation).map(|(result, _)| result)
}

/// The selected claim and proofs nested inside it remain strict. Separate
/// sibling claims restore the surrounding policy when their scope ends.
pub(super) struct ClaimScope {
    previous_strict: bool,
    _checked_only: CheckedOnlyScope,
    measurement: Option<ClaimMeasurement>,
}

struct ClaimMeasurement {
    selection: Rc<Selection>,
    started: Instant,
    _discovery: Option<ReplayDiscoveryScope>,
}

impl ClaimScope {
    pub(super) fn enter(label: &str) -> Self {
        let selected = SELECTION.with(|selection| {
            selection
                .borrow()
                .as_ref()
                .filter(|selection| crate::languages::claim_label_matches(label, &selection.label))
                .cloned()
        });
        if let Some(selected) = &selected {
            selected.visited.set(true);
        }
        let previous_strict = STRICT_CLAIM.with(|strict| {
            strict.replace(strict.get() || selected.as_ref().is_some_and(|s| s.strict))
        });
        let checked_only =
            CheckedOnlyScope::enter(selected.as_ref().is_some_and(|s| s.checked_only));
        let measurement = selected.and_then(|selected| {
            let replay = selected.replay.as_ref()?;
            let discovery = selected
                .strict
                .then(|| ReplayDiscoveryScope::enter(&replay.discovery));
            Some(ClaimMeasurement {
                selection: selected,
                started: Instant::now(),
                _discovery: discovery,
            })
        });
        Self {
            previous_strict,
            _checked_only: checked_only,
            measurement,
        }
    }
}

impl Drop for ClaimScope {
    fn drop(&mut self) {
        if let Some(measurement) = self.measurement.take() {
            let elapsed = &measurement
                .selection
                .replay
                .as_ref()
                .expect("measured claim")
                .elapsed;
            elapsed.set(elapsed.get() + measurement.started.elapsed());
        }
        STRICT_CLAIM.with(|strict| strict.set(self.previous_strict));
    }
}

/// Checks one claim without implicit solving, while unrelated proof units
/// keep their ordinary policy. `claim_label` is the proof's runtime/source
/// inventory label. A successful operation must have checked that claim;
/// an unknown label fails rather than silently leaving automation enabled.
/// The unconditional [`super::without_implicit_solve`] scope still takes
/// precedence, including inside an unselected claim.
pub fn without_implicit_solve_for_claim<R>(
    claim_label: &str,
    operation: impl FnOnce() -> Result<R, String>,
) -> Result<R, String> {
    check_selected_claim(claim_label, true, false, false, operation).map(|(result, _)| result)
}

/// Cold-checks an audit claim and measures time spent inside its proof scope.
/// Complete rewrites also reject search and monitored discovery.
pub fn check_audit_claim<R>(
    claim_label: &str,
    complete_rewrite: bool,
    operation: impl FnOnce() -> Result<R, String>,
) -> Result<(R, Duration), String> {
    check_selected_claim(
        claim_label,
        complete_rewrite,
        true,
        complete_rewrite,
        operation,
    )
}

fn check_selected_claim<R>(
    claim_label: &str,
    strict: bool,
    measure_replay: bool,
    checked_only: bool,
    operation: impl FnOnce() -> Result<R, String>,
) -> Result<(R, Duration), String> {
    struct Restore(Option<Rc<Selection>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            SELECTION.with(|selection| *selection.borrow_mut() = self.0.take());
        }
    }
    let selected = Rc::new(Selection {
        label: claim_label.to_string(),
        visited: Cell::new(false),
        strict,
        checked_only,
        replay: measure_replay.then(ReplayMeasurement::default),
    });
    let _restore =
        Restore(SELECTION.with(|selection| selection.borrow_mut().replace(Rc::clone(&selected))));
    let result = operation();
    if let Some(discovery) = selected
        .replay
        .as_ref()
        .and_then(|replay| replay.discovery.borrow_mut().take())
    {
        return Err(format!(
            "expanded claim `{claim_label}` {discovery}; write the selected evidence explicitly"
        ));
    }
    let result = result?;
    if !selected.visited.get() {
        return Err(format!(
            "cold checking did not visit selected proof `{claim_label}`"
        ));
    }
    Ok((
        result,
        selected
            .replay
            .as_ref()
            .map_or(Duration::ZERO, |replay| replay.elapsed.get()),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn audit_rejects_nested_ambient_discovery_only_in_complete_rewrites() {
        let query = || {
            let context = crate::kernel::PureFactContext::new();
            crate::kernel::search::disjunction_candidates(&context).count()
        };
        let replay = |strict, inside| {
            {
                let _neighbor = ClaimScope::enter("neighbor.contract");
                assert!(!checked_only());
                assert_eq!(query(), 0);
            }
            {
                let _selected = ClaimScope::enter("selected.contract");
                assert_eq!(selected_claim_is_strict(), strict);
                assert_eq!(checked_only(), strict);
                if inside {
                    let _nested = ClaimScope::enter("nested.ensures_0");
                    assert_eq!(checked_only(), strict);
                    assert_eq!(query(), 0);
                }
            }
            assert!(!selected_claim_is_strict());
            assert!(!checked_only());
            assert_eq!(query(), 0);
            Ok(())
        };
        check_audit_claim("selected.contract", true, || replay(true, false)).unwrap();
        let error =
            check_audit_claim("selected.contract", true, || replay(true, true)).unwrap_err();
        assert!(error.contains("selected.contract"), "{error}");
        assert!(error.contains("ambient fact search"), "{error}");
        check_audit_claim("selected.contract", false, || replay(false, true)).unwrap();
        assert_eq!(query(), 0);
    }
}
