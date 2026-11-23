//! Build-time ratchet for read identity (`design/point-named-reads.md`, P0).
//!
//! A read term's name decides which reads the prover treats as one term, so
//! reads are to be built by one constructor, `MachineTerm::read_at`. Each file
//! may build `MachineTerm::MemoryLoad(..)` directly at most as often as
//! [`BASELINE`] says, outside test code. Converting a site lowers its count;
//! the table must then be lowered to match, so it never grows back.

use std::collections::BTreeMap;
use syn::visit::Visit;

/// Direct constructions per file. Lower an entry when converting sites;
/// never raise one.
const BASELINE: &[(&str, usize)] = &[
    // `MachineTerm::read_named` itself.
    ("src/kernel/primitives/machine_integer.rs", 1),
];

/// Direct `MemoryLoad(..)` constructions in `file`, outside test code.
pub(super) fn count(file: &syn::File) -> usize {
    let mut counter = Counter { count: 0 };
    counter.visit_file(file);
    counter.count
}

/// Each file's count must equal its baseline entry (zero when absent).
pub(super) fn check(counts: &BTreeMap<String, usize>) -> Result<(), Vec<String>> {
    let baseline: BTreeMap<&str, usize> = BASELINE.iter().copied().collect();
    let mut errors = Vec::new();
    for (path, &found) in counts {
        let expected = baseline.get(path.as_str()).copied().unwrap_or(0);
        if found > expected {
            errors.push(format!(
                "{path}: {found} direct `MachineTerm::MemoryLoad(..)` constructions, {expected} allowed; build reads with `MachineTerm::read_at` (build_support/read_construction.rs)"
            ));
        } else if found < expected {
            errors.push(format!(
                "{path}: {found} direct `MachineTerm::MemoryLoad(..)` constructions; lower its entry in build_support/read_construction.rs from {expected} to {found}"
            ));
        }
    }
    for (path, expected) in &baseline {
        if !counts.contains_key(*path) {
            errors.push(format!(
                "{path}: no direct `MachineTerm::MemoryLoad(..)` constructions left; remove its entry ({expected}) from build_support/read_construction.rs"
            ));
        }
    }
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

struct Counter {
    count: usize,
}

impl<'ast> Visit<'ast> for Counter {
    fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
        if !super::test_only(&item.attrs) {
            syn::visit::visit_item_mod(self, item);
        }
    }
    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        if !super::test_only(&item.attrs) {
            syn::visit::visit_item_fn(self, item);
        }
    }
    fn visit_impl_item_fn(&mut self, item: &'ast syn::ImplItemFn) {
        if !super::test_only(&item.attrs) {
            syn::visit::visit_impl_item_fn(self, item);
        }
    }
    fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
        if let syn::Expr::Path(path) = call.func.as_ref()
            && path
                .path
                .segments
                .last()
                .is_some_and(|segment| segment.ident == "MemoryLoad")
        {
            self.count += 1;
        }
        syn::visit::visit_expr_call(self, call);
    }
}
