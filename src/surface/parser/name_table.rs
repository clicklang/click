//! The lexical names a file binds while it is parsed, indexed by kind.
//!
//! Each kind keeps its own index, so a block can set one kind aside and
//! restore it in constant time, and a question about a name across kinds,
//! such as whether anything visible already binds it, is one query here.

use std::collections::BTreeSet;

/// A kind of lexical binding the parser tracks by name.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum NameKind {
    /// A proof binder in the current proof block: an `obtain` variable, an
    /// unfold witness or field output.
    ProofBinder,
    /// A name a contract expression reads as a value: a C parameter or local
    /// in scope, a pattern binder, an `obtain` variable of C or algebraic type.
    ContractBinding,
    /// A theorem or contract parameter of `Integer` type.
    IntegerParameter,
    /// A `let` or binder of `Integer` type.
    IntegerLet,
    /// Any parameter of the theorem being parsed.
    TheoremParameter,
}

const KINDS: usize = 5;

impl NameKind {
    /// Every kind.
    pub(super) const ALL: &'static [NameKind] = &[
        NameKind::ProofBinder,
        NameKind::ContractBinding,
        NameKind::IntegerParameter,
        NameKind::IntegerLet,
        NameKind::TheoremParameter,
    ];
    /// A C or pure value a contract expression reads by name.
    pub(super) const VALUES: &'static [NameKind] = &[
        NameKind::ContractBinding,
        NameKind::IntegerParameter,
        NameKind::IntegerLet,
    ];
    /// An `Integer` parameter or `let`.
    pub(super) const INTEGERS: &'static [NameKind] =
        &[NameKind::IntegerParameter, NameKind::IntegerLet];
}

impl NameKind {
    fn index(self) -> usize {
        match self {
            NameKind::ProofBinder => 0,
            NameKind::ContractBinding => 1,
            NameKind::IntegerParameter => 2,
            NameKind::IntegerLet => 3,
            NameKind::TheoremParameter => 4,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(super) struct NameTable {
    names: [BTreeSet<String>; KINDS],
}

impl NameTable {
    pub(super) fn contains(&self, kind: NameKind, name: &str) -> bool {
        self.names[kind.index()].contains(name)
    }

    /// Whether `name` has a binding of any of `kinds`.
    pub(super) fn contains_any(&self, kinds: &[NameKind], name: &str) -> bool {
        kinds.iter().any(|kind| self.contains(*kind, name))
    }

    pub(super) fn insert(&mut self, kind: NameKind, name: String) -> bool {
        self.names[kind.index()].insert(name)
    }

    pub(super) fn remove(&mut self, kind: NameKind, name: &str) -> bool {
        self.names[kind.index()].remove(name)
    }

    pub(super) fn extend(&mut self, kind: NameKind, names: impl IntoIterator<Item = String>) {
        self.names[kind.index()].extend(names);
    }

    #[cfg(test)]
    pub(super) fn is_empty(&self, kind: NameKind) -> bool {
        self.names[kind.index()].is_empty()
    }

    /// Sets `kind`'s bindings aside, leaving none, for a block to restore.
    pub(super) fn take(&mut self, kind: NameKind) -> BTreeSet<String> {
        std::mem::take(&mut self.names[kind.index()])
    }

    /// Replaces `kind`'s bindings, returning the previous ones.
    pub(super) fn replace(&mut self, kind: NameKind, names: BTreeSet<String>) -> BTreeSet<String> {
        std::mem::replace(&mut self.names[kind.index()], names)
    }
}
