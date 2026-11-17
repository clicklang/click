//! Lexically scoped names: the one place a binding hides an earlier binding
//! of its name and is undone when its scope ends.
//!
//! A scope is entered by taking a [`Scope`] mark, and every binding or
//! hiding after the mark is recorded with the value it replaced. Ending the
//! scope undoes them in reverse, so an inner scope never copies the names
//! of the scopes around it, and leaving it costs only what it bound.

#[cfg(test)]
use std::collections::BTreeMap;

/// A point in a lexical binding log; ending it undoes what came after.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[must_use = "a scope is ended with `ScopedNames::end`"]
pub(in crate::surface) struct Scope(pub(super) usize);

#[cfg(test)]
use super::binders::ScopedBinders as ScopedNames;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_scope_ends_its_bindings_and_hidings_newest_first() {
        let mut names = ScopedNames::new(BTreeMap::from([("x".to_string(), 1)]).into());
        let outer = names.scope();
        names.bind("x", 2);
        names.bind("y", 3);
        let inner = names.scope();
        names.hide("x");
        names.bind("y", 4);
        assert_eq!(names.get("x"), None);
        assert_eq!(names.get("y"), Some(&4));
        names.end(inner);
        assert_eq!(names.get("x"), Some(&2));
        assert_eq!(names.get("y"), Some(&3));
        let mut seen = Vec::new();
        names.end_with(outer, |name, value| {
            seen.push((name.to_string(), value.copied()))
        });
        assert_eq!(
            names.names(),
            &super::super::BinderMap::from(BTreeMap::from([("x".to_string(), 1)]))
        );
        assert_eq!(seen, [("y".to_string(), None), ("x".to_string(), Some(1))]);
    }
}
