//! The constructed algebraic values whose fields were evaluated under a
//! requirement (`SpecExpression::Requires`): a Rust subslice
//! `bytes[a..b]`, built as `Slice::Slice(bytes + a, b - a)` with its length
//! owing `a <= b <= bytes.len()`.
//!
//! The registry names a value where it is introduced, so a printer spells
//! it as the form that built it by one lookup, never by searching the facts
//! for a spelling. An entry is recorded where the constructor is evaluated,
//! the same place its requirement is owed; a value with no entry is spelled
//! as its constructor. The registry is session state: a session entry
//! clears it, and a reusable session captures and restores it.

use super::*;

thread_local! {
    static REQUIRED_CONSTRUCTIONS: std::cell::RefCell<
        crate::persistent::PersistentMap<AlgebraicTerm, ()>,
    > = std::cell::RefCell::new(crate::persistent::PersistentMap::default());
}

/// The registry's contents, captured with a verification session's state.
pub(in crate::kernel) type RequiredConstructionsState =
    crate::persistent::PersistentMap<AlgebraicTerm, ()>;

/// Records that `value` was constructed with a field evaluated under a
/// requirement.
pub(super) fn record_required_construction(value: &AlgebraicTerm) {
    crate::instrumentation::record_deterministic_work(1);
    REQUIRED_CONSTRUCTIONS.with(|registry| {
        let mut registry = registry.borrow_mut();
        if registry.get(value).is_none() {
            registry.insert(value.clone(), ());
        }
    });
}

/// Whether `value` was constructed with a field evaluated under a
/// requirement in this session: one lookup.
pub fn is_required_construction(value: &AlgebraicTerm) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    REQUIRED_CONSTRUCTIONS.with(|registry| registry.borrow().get(value).is_some())
}

/// Whether `field`, a constructor field, is evaluated under a requirement.
pub(super) fn field_is_required(field: &SpecAlgebraicValue) -> bool {
    matches!(
        field,
        SpecAlgebraicValue::Program(SpecExpression::Requires { .. })
    )
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
