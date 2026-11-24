//! Build-time ratchet for read identity (`design/point-named-reads.md`, P0,
//! and `design/loads.md`, "Terms").
//!
//! A read term's name decides which reads the prover treats as one term, so
//! reads are to be built by one constructor each:
//!
//! - integer and float reads, `MachineTerm::MemoryLoad(..)`, by
//!   `MachineTerm::read_named` (and `MachineTerm::memory_read`, which calls it);
//! - their operands, the producer's `ReadPoint(..)` and the `LoadCell { .. }`
//!   that holds the read's interned load, by `read_operands`, which only
//!   `MachineTerm::read_named` calls (`design/loads.md`, step 3a);
//! - loads, `Load { .. }`, by `Load::at`, and pointer bases,
//!   `AddressBase::Load(..)`, by `Load::base`.
//!
//! Each file may build each form directly at most as often as [`BASELINE`]
//! says, outside test code. Converting a site lowers its count; the table
//! must then be lowered to match, so it never grows back.

use std::collections::BTreeMap;
use syn::visit::Visit;

/// A directly built read form, and the constructor that builds it.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum Form {
    MemoryLoad,
    ReadOperands,
    ReadPoint,
    LoadCell,
    Load,
    LoadBase,
}

impl Form {
    fn spelling(self) -> &'static str {
        match self {
            Self::MemoryLoad => "`MachineTerm::MemoryLoad(..)`",
            Self::ReadOperands => "`read_operands(..)` calls",
            Self::ReadPoint => "`ReadPoint(..)`",
            Self::LoadCell => "`LoadCell { .. }`",
            Self::Load => "`Load { .. }`",
            Self::LoadBase => "`AddressBase::Load(..)`",
        }
    }

    fn constructor(self) -> &'static str {
        match self {
            Self::MemoryLoad => "`MachineTerm::read_named`",
            Self::ReadOperands => "`MachineTerm::read_named`",
            Self::ReadPoint | Self::LoadCell => "`read_operands`",
            Self::Load => "`Load::at`",
            Self::LoadBase => "`Load::base`",
        }
    }
}

/// Direct constructions per file and form. Lower an entry when converting
/// sites; never raise one.
const BASELINE: &[(&str, Form, usize)] = &[
    // `MachineTerm::read_named` itself, which builds the read's operands
    // with `read_operands`.
    (
        "src/kernel/primitives/machine_integer.rs",
        Form::MemoryLoad,
        1,
    ),
    (
        "src/kernel/primitives/machine_integer.rs",
        Form::ReadOperands,
        1,
    ),
    // `read_operands` itself.
    ("src/kernel/primitives/load.rs", Form::ReadPoint, 1),
    ("src/kernel/primitives/load.rs", Form::LoadCell, 1),
    // `Load::at` and `Load::base` themselves.
    ("src/kernel/primitives/load.rs", Form::Load, 1),
    ("src/kernel/primitives/load.rs", Form::LoadBase, 1),
];

/// Direct constructions of each form in `file`, outside test code.
pub(super) fn count(file: &syn::File) -> BTreeMap<Form, usize> {
    let mut counter = Counter {
        counts: BTreeMap::new(),
        in_address_base_impl: false,
    };
    counter.visit_file(file);
    counter.counts
}

/// Each file's count of each form must equal its baseline entry (zero when
/// absent).
pub(super) fn check(counts: &BTreeMap<(String, Form), usize>) -> Result<(), Vec<String>> {
    let baseline: BTreeMap<(&str, Form), usize> = BASELINE
        .iter()
        .map(|(path, form, count)| ((*path, *form), *count))
        .collect();
    let mut errors = Vec::new();
    for ((path, form), &found) in counts {
        let expected = baseline.get(&(path.as_str(), *form)).copied().unwrap_or(0);
        let (spelling, constructor) = (form.spelling(), form.constructor());
        if found > expected {
            errors.push(format!(
                "{path}: {found} direct {spelling} constructions, {expected} allowed; build them with {constructor} (build_support/read_construction.rs)"
            ));
        } else if found < expected {
            errors.push(format!(
                "{path}: {found} direct {spelling} constructions; lower its entry in build_support/read_construction.rs from {expected} to {found}"
            ));
        }
    }
    for ((path, form), expected) in &baseline {
        if !counts.contains_key(&(path.to_string(), *form)) {
            errors.push(format!(
                "{path}: no direct {} constructions left; remove its entry ({expected}) from build_support/read_construction.rs",
                form.spelling()
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
    counts: BTreeMap<Form, usize>,
    /// Inside `impl AddressBase`, where `Self::Load(..)` builds the variant.
    in_address_base_impl: bool,
}

impl Counter {
    fn add(&mut self, form: Form) {
        *self.counts.entry(form).or_default() += 1;
    }
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
    fn visit_item_impl(&mut self, item: &'ast syn::ItemImpl) {
        if super::test_only(&item.attrs) {
            return;
        }
        let outer = self.in_address_base_impl;
        self.in_address_base_impl = matches!(item.self_ty.as_ref(), syn::Type::Path(path)
            if path.path.segments.last().is_some_and(|segment| segment.ident == "AddressBase"));
        syn::visit::visit_item_impl(self, item);
        self.in_address_base_impl = outer;
    }
    fn visit_impl_item_fn(&mut self, item: &'ast syn::ImplItemFn) {
        if !super::test_only(&item.attrs) {
            syn::visit::visit_impl_item_fn(self, item);
        }
    }
    fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
        if let syn::Expr::Path(path) = call.func.as_ref() {
            let segments: Vec<_> = path.path.segments.iter().map(|s| &s.ident).collect();
            match segments.as_slice() {
                [.., last] if *last == "MemoryLoad" => self.add(Form::MemoryLoad),
                [.., last] if *last == "read_operands" => self.add(Form::ReadOperands),
                [.., last] if *last == "ReadPoint" => self.add(Form::ReadPoint),
                [.., owner, last]
                    if *last == "Load"
                        && (*owner == "AddressBase"
                            || (*owner == "Self" && self.in_address_base_impl)) =>
                {
                    self.add(Form::LoadBase)
                }
                _ => {}
            }
        }
        syn::visit::visit_expr_call(self, call);
    }
    fn visit_expr_struct(&mut self, expression: &'ast syn::ExprStruct) {
        match expression.path.segments.last() {
            Some(segment) if segment.ident == "Load" => self.add(Form::Load),
            Some(segment) if segment.ident == "LoadCell" => self.add(Form::LoadCell),
            _ => {}
        }
        syn::visit::visit_expr_struct(self, expression);
    }
}
