//! The declaration table: every name a file and its library declare at the
//! top level, with the one kind it has.
//!
//! Each declaration enters the table once, through [`DeclarationTable::declare`],
//! which refuses a name already declared (as the same kind or another), and a
//! name the language reserves for that kind. The per-kind arity maps are the
//! views validation reads; no other place decides whether a name may be
//! declared.

use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::surface) enum DeclarationKind {
    Predicate,
    Contract,
    Function,
    Resource,
    Theorem,
}

impl DeclarationKind {
    fn noun(self) -> &'static str {
        match self {
            Self::Predicate => "predicate",
            Self::Contract => "contract",
            Self::Function => "function",
            Self::Resource => "resource",
            Self::Theorem => "theorem",
        }
    }
}

#[derive(Default)]
pub(in crate::surface) struct DeclarationTable {
    kinds: BTreeMap<String, DeclarationKind>,
    predicates: BTreeMap<String, usize>,
    contracts: BTreeMap<String, usize>,
    functions: BTreeMap<String, usize>,
    resources: BTreeMap<String, usize>,
    theorems: BTreeMap<String, usize>,
}

impl DeclarationTable {
    /// Declares `name` as `kind` taking `arity` arguments, or refuses it.
    pub(in crate::surface) fn declare(
        &mut self,
        kind: DeclarationKind,
        name: &str,
        arity: usize,
    ) -> Result<(), ClickError> {
        refuse_reserved_name(kind, name)?;
        if let Some(&existing) = self.kinds.get(name) {
            if existing == kind {
                return Err(ClickError::new(format!(
                    "duplicate {} definition `{name}`",
                    kind.noun()
                )));
            }
            return Err(ClickError::new(format!(
                "`{name}` is defined as both a {} and a {}",
                existing.noun(),
                kind.noun()
            )));
        }
        self.kinds.insert(name.to_string(), kind);
        self.arities_mut(kind).insert(name.to_string(), arity);
        Ok(())
    }

    /// The declared names of `kind`, each with its arity.
    pub(in crate::surface) fn arities(&self, kind: DeclarationKind) -> &BTreeMap<String, usize> {
        match kind {
            DeclarationKind::Predicate => &self.predicates,
            DeclarationKind::Contract => &self.contracts,
            DeclarationKind::Function => &self.functions,
            DeclarationKind::Resource => &self.resources,
            DeclarationKind::Theorem => &self.theorems,
        }
    }

    fn arities_mut(&mut self, kind: DeclarationKind) -> &mut BTreeMap<String, usize> {
        match kind {
            DeclarationKind::Predicate => &mut self.predicates,
            DeclarationKind::Contract => &mut self.contracts,
            DeclarationKind::Function => &mut self.functions,
            DeclarationKind::Resource => &mut self.resources,
            DeclarationKind::Theorem => &mut self.theorems,
        }
    }
}

fn refuse_reserved_name(kind: DeclarationKind, name: &str) -> Result<(), ClickError> {
    match kind {
        DeclarationKind::Predicate | DeclarationKind::Contract => {
            if matches!(
                name,
                "same_object" | crate::kernel::SAME_OBJECT_PREDICATE_NAME
            ) {
                return Err(ClickError::new(
                    "`same_object` is a built-in proposition and cannot be redefined",
                ));
            }
            if matches!(name, "held" | crate::kernel::MUTEX_HELD_PREDICATE_NAME) {
                return Err(ClickError::new(
                    "`held` is a built-in proposition and cannot be redefined",
                ));
            }
        }
        DeclarationKind::Function => {
            if is_integer_truncation(name) {
                return Err(ClickError::new(format!(
                    "`{name}` is a built-in Integer truncation name"
                )));
            }
            if is_integer_conversion(name) || name == "to_nat" {
                return Err(ClickError::new(format!(
                    "`{name}` is a built-in Integer conversion name"
                )));
            }
        }
        DeclarationKind::Resource => {
            if matches!(name, "read" | "write") {
                return Err(ClickError::new(format!(
                    "`{name}` is a built-in resource name"
                )));
            }
        }
        DeclarationKind::Theorem => {
            if matches!(
                name,
                "integer_range_fold_empty" | "integer_range_fold_append"
            ) {
                return Err(ClickError::new(format!(
                    "`{name}` names a law the kernel supplies, and a citation of it applies that law; rename the theorem"
                )));
            }
        }
    }
    if matches!(kind, DeclarationKind::Predicate | DeclarationKind::Function)
        && BUILTIN_CALL_FORMS.contains(&name)
    {
        return Err(ClickError::new(format!(
            "`{name}(...)` is a built-in form, so a {} named `{name}` could never be called; rename it",
            kind.noun()
        )));
    }
    Ok(())
}

/// The names the parser reads as a built-in form when applied, `defined(x)`
/// or `old(e)`. A predicate or function of one could never be called: the
/// form would be read in its place.
const BUILTIN_CALL_FORMS: &[&str] = &[
    "address",
    "aligned",
    "at",
    "byte_offset",
    "contains",
    "defined",
    "memory",
    "object",
    "old",
    "separate",
    "sizeof",
    "viewable",
];
