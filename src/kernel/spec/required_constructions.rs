//! The slices built under a requirement (`SpecExpression::Requires`
//! around `SpecExpression::SliceFromRawParts`): a Rust subslice
//! `bytes[a..b]`, built as `slice::from_raw_parts(bytes.as_ptr() + a, b -
//! a)` owing `a <= b <= bytes.len()` (`design/rust-slice-values.md`).
//!
//! The registry names a value where it is introduced, so a printer spells
//! it as the form that built it by one lookup, never by searching the facts
//! for a spelling. An entry is recorded where the slice is built, the same
//! place its requirement is owed; a slice with no entry is spelled as its
//! construction. The registry is session state: a session entry
//! clears it, and a reusable session captures and restores it.

use super::*;

thread_local! {
    static REQUIRED_CONSTRUCTIONS: std::cell::RefCell<
        crate::persistent::PersistentMap<Pointer, ()>,
    > = std::cell::RefCell::new(crate::persistent::PersistentMap::default());
}

/// The registry's contents, captured with a verification session's state.
pub(in crate::kernel) type RequiredConstructionsState =
    crate::persistent::PersistentMap<Pointer, ()>;

/// Records that the slice `value` was built under a requirement.
pub(super) fn record_required_construction(value: &Pointer) {
    crate::instrumentation::record_deterministic_work(1);
    REQUIRED_CONSTRUCTIONS.with(|registry| {
        let mut registry = registry.borrow_mut();
        if registry.get(value).is_none() {
            registry.insert(value.clone(), ());
        }
    });
}

/// Whether the slice `value` was built under a requirement in this session:
/// one lookup.
pub fn is_required_construction(value: &Pointer) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    REQUIRED_CONSTRUCTIONS.with(|registry| registry.borrow().get(value).is_some())
}

pub(in crate::kernel) fn clear_required_constructions() {
    REQUIRED_CONSTRUCTIONS.with(|registry| *registry.borrow_mut() = Default::default());
}

pub(in crate::kernel) fn capture_required_constructions() -> RequiredConstructionsState {
    REQUIRED_CONSTRUCTIONS.with(|registry| registry.borrow().clone())
}

pub(in crate::kernel) fn restore_required_constructions(state: &RequiredConstructionsState) {
    REQUIRED_CONSTRUCTIONS.with(|registry| *registry.borrow_mut() = state.clone());
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/spec/required_constructions.rs");
}
