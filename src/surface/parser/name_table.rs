//! The lexical names a file binds while it is parsed.
//!
//! Plain names are indexed by [`NameKind`]; names that carry data
//! (resource instances, C parameter types, struct and aggregate parameters,
//! arm binder types, facts) are maps beside them. Each kind keeps its own
//! index, so a block can set one kind aside and restore it in constant time.
//! A question about a name across kinds, such as whether anything visible
//! already binds it, is one query here, and so is hiding an earlier binding
//! and restoring it when the hiding binder's block ends.

use super::*;

/// A binding a proof binder hid, put back when the binder's block ends.
#[derive(Clone, Debug)]
pub(super) enum ShadowRestore {
    /// A fact name: its previous proposition, or none when `have` bound it
    /// fresh and its block's end ends it.
    Fact {
        name: String,
        previous: Option<ClickProposition>,
    },
    /// A resource instance a value binder of the same spelling hid.
    Resource {
        name: String,
        binding: (Variable, String),
        target: Option<ResourceClause>,
    },
}

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
    /// A C parameter of `void*` type.
    VoidPointerParameter,
    /// A C parameter that is an array of structs.
    StructArrayParameter,
    /// A C++ or Rust reference parameter, which names what it refers to.
    ReferenceParameter,
    /// A declaration's type parameter.
    TypeParameter,
}

const KINDS: usize = 9;

impl NameKind {
    /// The kinds that bind a value a proposition can read by name, which a
    /// `have` fact name may not take.
    pub(super) const BOUND: &'static [NameKind] = &[
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
            NameKind::VoidPointerParameter => 5,
            NameKind::StructArrayParameter => 6,
            NameKind::ReferenceParameter => 7,
            NameKind::TypeParameter => 8,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(super) struct NameTable {
    names: [BTreeSet<String>; KINDS],
    pub(super) resource_bindings: BTreeMap<String, (Variable, String)>,
    pub(super) resource_fields: BTreeMap<String, ResourceFieldAccess>,
    pub(super) resource_targets: BTreeMap<String, ResourceClause>,
    /// The current function block's value binders, `views s: R(a, _);`.
    pub(super) value_binders: BTreeMap<String, ValueBinder>,
    /// Their declaration order, for the function block.
    pub(super) value_binder_order: Vec<String>,
    pub(super) struct_params: BTreeMap<String, String>,
    pub(super) c_parameter_types: BTreeMap<String, C0Type>,
    /// The struct each `void *` parameter has been cast to so far; the
    /// parameters themselves are `NameKind::VoidPointerParameter` names.
    pub(super) parameter_struct_casts: BTreeMap<String, String>,
    pub(super) aggregate_objects: BTreeMap<String, String>,
    pub(super) global_array_shapes: BTreeMap<String, GlobalArrayShape>,
    pub(super) algebraic_params: BTreeMap<String, (AlgebraicTypeApplication, usize)>,
    /// The C names (parameters, locals and file-scope objects) visible to the
    /// C function block being parsed. `true` and `false` are specification
    /// literals unless one of these names spells them.
    pub(super) c_object_names: Option<std::sync::Arc<BTreeSet<String>>>,
    /// The constructor bindings of the match arm currently being parsed, with
    /// their declared field types. A struct-pointer binding is also in
    /// `struct_params`; the others are here only so using one as a
    /// memory base is refused by name instead of lowering to a width-unknown
    /// load.
    pub(super) arm_binding_types: BTreeMap<String, AlgebraicFieldType>,
    /// The facts `have name: P` named, visible from the `have` to the end
    /// of its block, nested blocks included. A citation by name is read as
    /// the proposition, exactly as if it were restated there.
    pub(super) fact_names: BTreeMap<String, ClickProposition>,
    /// The bindings each name shadowed, undone when its block ends.
    pub(super) fact_name_restores: Vec<ShadowRestore>,
    pub(super) ended_fact_names: BTreeSet<String>,
    /// Names whose `have` proof is being parsed, and names whose block has
    /// ended inside the current proof, so citing one is refused by name
    /// rather than read as an unbound variable.
    pub(super) fact_names_being_proved: BTreeSet<String>,
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

    /// Whether `name` is a C parameter or a C object of the function block
    /// being parsed.
    pub(super) fn is_c_variable(&self, name: &str) -> bool {
        self.c_parameter_types.contains_key(name)
            || self
                .c_object_names
                .as_ref()
                .is_some_and(|names| names.contains(name))
    }

    /// Whether anything visible binds `name` as a value a proposition can
    /// read: a parameter, a C variable, a contract or proof binding, a
    /// resource instance or a match-arm binder.
    pub(super) fn is_bound(&self, name: &str) -> bool {
        self.contains_any(NameKind::BOUND, name)
            || self.resource_bindings.contains_key(name)
            || self.arm_binding_types.contains_key(name)
            || self.is_c_variable(name)
    }

    /// Every name of `kind`.
    pub(super) fn set(&self, kind: NameKind) -> &BTreeSet<String> {
        &self.names[kind.index()]
    }

    /// Sets `kind`'s bindings aside, leaving none, for a block to restore.
    pub(super) fn take(&mut self, kind: NameKind) -> BTreeSet<String> {
        std::mem::take(&mut self.names[kind.index()])
    }

    /// Replaces `kind`'s bindings, returning the previous ones.
    pub(super) fn replace(&mut self, kind: NameKind, names: BTreeSet<String>) -> BTreeSet<String> {
        std::mem::replace(&mut self.names[kind.index()], names)
    }

    /// Ends the fact names bound since `checkpoint` and puts back each fact
    /// or resource a later binder hid.
    pub(super) fn restore_fact_names(&mut self, checkpoint: usize) {
        while self.fact_name_restores.len() > checkpoint {
            match self
                .fact_name_restores
                .pop()
                .expect("restore above checkpoint")
            {
                ShadowRestore::Fact {
                    name,
                    previous: Some(proposition),
                } => {
                    self.fact_names.insert(name, proposition);
                }
                ShadowRestore::Fact {
                    name,
                    previous: None,
                } => {
                    self.fact_names.remove(&name);
                    self.ended_fact_names.insert(name);
                }
                ShadowRestore::Resource {
                    name,
                    binding,
                    target,
                } => {
                    if let Some(target) = target {
                        self.resource_targets.insert(name.clone(), target);
                    }
                    self.resource_bindings.insert(name, binding);
                }
            }
        }
    }

    /// Hides the fact, and for a value binder the resource instance, that
    /// `name` names, until the block that binds it ends. `intro() as` uses
    /// this directly: an introduced binder may hide a C parameter, which
    /// `outer.name` still reaches.
    pub(super) fn hide_for_proof_binder(&mut self, name: &str, resource: bool) {
        if let Some(previous) = self.fact_names.remove(name) {
            self.fact_name_restores.push(ShadowRestore::Fact {
                name: name.to_string(),
                previous: Some(previous),
            });
        }
        if !resource && let Some(binding) = self.resource_bindings.remove(name) {
            let target = self.resource_targets.remove(name);
            self.fact_name_restores.push(ShadowRestore::Resource {
                name: name.to_string(),
                binding,
                target,
            });
        }
    }
}
