//! Carries a compatibility call lookup's selected head to the proof driver.
//! This is presentation input. The driver must check any written unfold
//! and the ensuing call afresh.

use super::ResourceFact;
use std::cell::RefCell;

enum Selection {
    Ordinary,
    Capture(Vec<ResourceFact>),
    Disabled,
}

thread_local! {
    static SELECTION: RefCell<Selection> = const { RefCell::new(Selection::Ordinary) };
}

fn with_selection<T>(mode: Selection, operation: impl FnOnce() -> T) -> (T, Selection) {
    struct Restore(Selection);
    impl Drop for Restore {
        fn drop(&mut self) {
            SELECTION
                .with(|slot| slot.replace(std::mem::replace(&mut self.0, Selection::Ordinary)));
        }
    }
    let _restore = Restore(SELECTION.with(|slot| slot.replace(mode)));
    let result = operation();
    let selected = SELECTION.with(|slot| slot.replace(Selection::Ordinary));
    (result, selected)
}

pub(crate) fn capture<T>(operation: impl FnOnce() -> T) -> (T, Vec<ResourceFact>) {
    if !search_enabled() {
        return (operation(), Vec::new());
    }
    let (result, Selection::Capture(selected)) =
        with_selection(Selection::Capture(Vec::new()), operation)
    else {
        unreachable!("capture scope retains its selection")
    };
    (result, selected)
}

pub(crate) fn without_search<T>(operation: impl FnOnce() -> T) -> T {
    with_selection(Selection::Disabled, operation).0
}

pub(super) fn search_enabled() -> bool {
    SELECTION.with(|slot| !matches!(*slot.borrow(), Selection::Disabled))
}

pub(super) fn record(head: ResourceFact) {
    SELECTION.with(|slot| {
        if let Selection::Capture(selected) = &mut *slot.borrow_mut() {
            selected.push(head);
        }
    });
}
