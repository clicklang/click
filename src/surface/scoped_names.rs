//! Lexically scoped names: the one place a binding hides an earlier binding
//! of its name and is undone when its scope ends.
//!
//! A scope is entered by taking a [`Scope`] mark, and every binding or
//! hiding after the mark is recorded with the value it replaced. Ending the
//! scope undoes them in reverse, so an inner scope never copies the names
//! of the scopes around it, and leaving it costs only what it bound.

use std::collections::BTreeMap;

/// A point in a [`ScopedNames`] log; ending it undoes what came after.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[must_use = "a scope is ended with `ScopedNames::end`"]
pub(in crate::surface) struct Scope(usize);

#[derive(Clone, Debug)]
pub(in crate::surface) struct ScopedNames<V> {
    names: BTreeMap<String, V>,
    shadowed: Vec<(String, Option<V>)>,
}

impl<V> Default for ScopedNames<V> {
    fn default() -> Self {
        Self {
            names: BTreeMap::new(),
            shadowed: Vec::new(),
        }
    }
}

impl<V> ScopedNames<V> {
    /// Names bound in no scope, such as a declaration's parameters.
    pub(in crate::surface) fn new(names: BTreeMap<String, V>) -> Self {
        Self {
            names,
            shadowed: Vec::new(),
        }
    }

    /// Replaces every name with `names`, forgetting every open scope.
    pub(in crate::surface) fn reset(&mut self, names: impl IntoIterator<Item = (String, V)>) {
        self.names.clear();
        self.names.extend(names);
        self.shadowed.clear();
    }

    /// The mark of the current point, for [`Self::end`].
    pub(in crate::surface) fn scope(&self) -> Scope {
        Scope(self.shadowed.len())
    }

    /// Binds `name` to `value`, hiding any binding it had until the scope
    /// open at this call ends.
    pub(in crate::surface) fn bind(&mut self, name: &str, value: V) {
        let previous = self.names.insert(name.to_string(), value);
        self.shadowed.push((name.to_string(), previous));
    }

    /// Hides any binding `name` has until the scope open at this call ends.
    pub(in crate::surface) fn hide(&mut self, name: &str) {
        let previous = self.names.remove(name);
        self.shadowed.push((name.to_string(), previous));
    }

    /// Ends every binding and hiding since `scope`, newest first, restoring
    /// what each replaced. `restored` sees each name and the binding it has
    /// again, so a caller keeping a derived index can follow.
    pub(in crate::surface) fn end_with(
        &mut self,
        scope: Scope,
        mut restored: impl FnMut(&str, Option<&V>),
    ) {
        while self.shadowed.len() > scope.0 {
            let (name, previous) = self.shadowed.pop().expect("a binding above the scope");
            match previous {
                Some(value) => {
                    self.names.insert(name.clone(), value);
                }
                None => {
                    self.names.remove(&name);
                }
            }
            restored(&name, self.names.get(&name));
        }
    }

    /// Ends every binding and hiding since `scope`.
    pub(in crate::surface) fn end(&mut self, scope: Scope) {
        self.end_with(scope, |_, _| {});
    }

    /// The names bound now, each with its newest binding.
    pub(in crate::surface) fn names(&self) -> &BTreeMap<String, V> {
        &self.names
    }

    pub(in crate::surface) fn get(&self, name: &str) -> Option<&V> {
        self.names.get(name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_scope_ends_its_bindings_and_hidings_newest_first() {
        let mut names = ScopedNames::new(BTreeMap::from([("x".to_string(), 1)]));
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
        assert_eq!(names.names(), &BTreeMap::from([("x".to_string(), 1)]));
        assert_eq!(seen, [("y".to_string(), None), ("x".to_string(), Some(1))]);
    }
}
