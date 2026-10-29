//! Cold-check policy belongs to the selected source proof, not every proof
//! the targeted verifier visits while constructing its function environment.
use std::cell::{Cell, RefCell};
use std::rc::Rc;

struct Selection {
    label: String,
    visited: Cell<bool>,
}

thread_local! {
    static SELECTION: RefCell<Option<Rc<Selection>>> = const { RefCell::new(None) };
    static STRICT_CLAIM: Cell<bool> = const { Cell::new(false) };
}

pub(super) fn selected_claim_is_strict() -> bool {
    STRICT_CLAIM.with(Cell::get)
}

/// The selected claim and proofs nested inside it remain strict. Separate
/// sibling claims restore the surrounding policy when their scope ends.
pub(super) struct ClaimScope(bool);

impl ClaimScope {
    pub(super) fn enter(label: &str) -> Self {
        let selected = SELECTION.with(|selection| {
            selection.borrow().as_ref().is_some_and(|selection| {
                if selection.label == label {
                    selection.visited.set(true);
                    true
                } else {
                    false
                }
            })
        });
        Self(STRICT_CLAIM.with(|strict| strict.replace(strict.get() || selected)))
    }
}

impl Drop for ClaimScope {
    fn drop(&mut self) {
        STRICT_CLAIM.with(|strict| strict.set(self.0));
    }
}

/// Checks one claim without implicit automation, while unrelated proof units
/// keep their ordinary policy. `claim_label` is the proof's runtime/source
/// inventory label. A successful operation must have checked that claim;
/// an unknown label fails rather than silently leaving automation enabled.
/// The unconditional [`super::without_implicit_auto`] scope still takes
/// precedence, including inside an unselected claim.
pub fn without_implicit_auto_for_claim<R>(
    claim_label: &str,
    operation: impl FnOnce() -> Result<R, String>,
) -> Result<R, String> {
    struct Restore(Option<Rc<Selection>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            SELECTION.with(|selection| *selection.borrow_mut() = self.0.take());
        }
    }
    let selected = Rc::new(Selection {
        label: claim_label.to_string(),
        visited: Cell::new(false),
    });
    let _restore =
        Restore(SELECTION.with(|selection| selection.borrow_mut().replace(Rc::clone(&selected))));
    let result = operation()?;
    if !selected.visited.get() {
        return Err(format!(
            "cold checking did not visit selected proof `{claim_label}`"
        ));
    }
    Ok(result)
}
