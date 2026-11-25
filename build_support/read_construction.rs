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
//! Two further counts hold `design/loads.md`'s step 3b, which removes the
//! untyped eight-byte kind:
//!
//! - every `LoadKind::Bits64` written in an expression, a pattern or a macro,
//!   so that the kind is not used anew while the step classifies and
//!   converts its uses;
//! - calls of `legacy_pointer_word_read`, the one bridge by which a pointer
//!   cell still reaches the integer read machinery as an eight-byte read.
//!   A pointer load is named, compared and keyed as a `Load`; any other
//!   integer read built for a pointer cell is a detour.
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
    Bits64,
    PointerWordRead,
    UnplacedPoint,
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
            Self::Bits64 => "`LoadKind::Bits64` spellings",
            Self::PointerWordRead => "`legacy_pointer_word_read(..)` calls",
            Self::UnplacedPoint => {
                "`ProgramPoint::unplaced(..)`, `canonical_form_of_load(..)` and `memory_read(..)` calls"
            }
        }
    }

    /// What to do instead of adding one more of this form.
    fn advice(self) -> &'static str {
        match self {
            Self::MemoryLoad | Self::ReadOperands => "build them with `MachineTerm::read_named`",
            Self::ReadPoint | Self::LoadCell => "build them with `read_operands`",
            Self::Load => "build them with `Load::at`",
            Self::LoadBase => "build them with `Load::base`",
            Self::Bits64 => {
                "a 64-bit integer read takes its kind from its format, and a pointer load is a `Load` (design/loads.md, step 3b)"
            }
            Self::PointerWordRead => {
                "name, compare and key a pointer load as a `Load` (design/loads.md, step 3b)"
            }
            Self::UnplacedPoint => {
                "place the memory: `ProgramPoint::viewing` for a state or a view of one, `ProgramPoint::walked` for a legacy walk's memory (design/point-named-reads.md)"
            }
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
    // `LoadKind::Bits64`, classified for step 3b (`design/loads.md`).
    // The pointer-word bridge, the one remaining pointer-cell use.
    ("src/kernel/primitives/load.rs", Form::Bits64, 1),
    // Genuine 64-bit integer reads (step 3b, PR 4). The algebraic stand-in
    // is decoded at its own type, `LoadKind::Algebraic` (PR 2); two arms
    // still name it beside `Bits64` and a float, sharing the 64-bit width
    // (`term_width.rs`, `memory_loads.rs`'s producer equation).
    ("src/kernel/assumptions.rs", Form::Bits64, 1),
    (
        "src/kernel/assumptions/condition_reasoning/memory_conditions.rs",
        Form::Bits64,
        1,
    ),
    ("src/kernel/equality_graph.rs", Form::Bits64, 1),
    ("src/kernel/equality_graph/terms.rs", Form::Bits64, 2),
    ("src/kernel/eval/memory_loads.rs", Form::Bits64, 6),
    (
        "src/kernel/eval/memory_loads/read_observations.rs",
        Form::Bits64,
        1,
    ),
    ("src/kernel/memory_history.rs", Form::Bits64, 8),
    ("src/kernel/primitives/memory_state.rs", Form::Bits64, 2),
    ("src/kernel/primitives/program_point.rs", Form::Bits64, 2),
    ("src/kernel/primitives/term_width.rs", Form::Bits64, 1),
    ("src/surface/diagnostics.rs", Form::Bits64, 1),
    (
        "src/surface/proof/smart_closures/search.rs",
        Form::Bits64,
        1,
    ),
    ("src/surface/proof/surface_synthesis.rs", Form::Bits64, 4),
    (
        "src/surface/proof_diagnostics/render/surface.rs",
        Form::Bits64,
        2,
    ),
    // The two consumers that still ask the integer read machinery about a
    // pointer cell (`legacy_pointer_word_read`'s documentation).
    ("src/kernel/assumptions.rs", Form::PointerWordRead, 2),
    (
        "src/kernel/primitives/term_operations.rs",
        Form::PointerWordRead,
        2,
    ), // Points built from a bare memory, with no place (`ProgramPoint::unplaced`).
    // Each conversion to `viewing` or `walked` lowers its file's entry; the
    // constructor goes when the table has none.
    (
        "src/kernel/api/contract_certification/contract_claims.rs",
        Form::UnplacedPoint,
        1,
    ),
    ("src/kernel/assumptions.rs", Form::UnplacedPoint, 1),
    ("src/kernel/equality_graph.rs", Form::UnplacedPoint, 2),
    ("src/kernel/equality_graph/terms.rs", Form::UnplacedPoint, 1),
    ("src/kernel/eval/memory_loads.rs", Form::UnplacedPoint, 8),
    (
        "src/kernel/eval/memory_loads/read_observations.rs",
        Form::UnplacedPoint,
        5,
    ),
    ("src/kernel/memory_history.rs", Form::UnplacedPoint, 3),
    ("src/kernel/primitives.rs", Form::UnplacedPoint, 1),
    (
        "src/kernel/primitives/cell_store.rs",
        Form::UnplacedPoint,
        1,
    ),
    (
        "src/kernel/primitives/machine_integer.rs",
        Form::UnplacedPoint,
        1,
    ),
    (
        "src/kernel/primitives/memory_state.rs",
        Form::UnplacedPoint,
        6,
    ),
    (
        "src/kernel/primitives/program_point.rs",
        Form::UnplacedPoint,
        2,
    ),
    (
        "src/kernel/primitives/term_operations.rs",
        Form::UnplacedPoint,
        1,
    ),
    (
        "src/kernel/proof/equality_rewrite.rs",
        Form::UnplacedPoint,
        1,
    ),
    ("src/kernel/proof/execution.rs", Form::UnplacedPoint, 1),
    (
        "src/kernel/reasoning/substitution.rs",
        Form::UnplacedPoint,
        1,
    ),
    (
        "src/kernel/reasoning/variable_collection.rs",
        Form::UnplacedPoint,
        1,
    ),
    ("src/kernel/spec.rs", Form::UnplacedPoint, 1),
    (
        "src/surface/lowering/resource_lowering.rs",
        Form::UnplacedPoint,
        2,
    ),
    (
        "src/surface/proof/fixed_state_proofs/fact_transport.rs",
        Form::UnplacedPoint,
        1,
    ),
    (
        "src/surface/proof/smart_closures/search.rs",
        Form::UnplacedPoint,
        2,
    ),
    ("src/surface/proof_trace.rs", Form::UnplacedPoint, 1),
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
        let (spelling, advice) = (form.spelling(), form.advice());
        if found > expected {
            errors.push(format!(
                "{path}: {found} direct {spelling} constructions, {expected} allowed; {advice} (build_support/read_construction.rs)"
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
                [.., last] if *last == "legacy_pointer_word_read" => {
                    self.add(Form::PointerWordRead)
                }
                [.., owner, last]
                    if *last == "unplaced" && (*owner == "ProgramPoint" || *owner == "Self") =>
                {
                    self.add(Form::UnplacedPoint)
                }
                // The wrappers that build a read from a bare memory make an
                // unplaced point for each caller.
                [.., last] if *last == "canonical_form_of_load" || *last == "memory_read" => {
                    self.add(Form::UnplacedPoint)
                }
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
    // Expression and pattern paths: a pattern's path is an `ExprPath` too.
    fn visit_expr_path(&mut self, path: &'ast syn::ExprPath) {
        if names_bits64(path.path.segments.iter().map(|segment| &segment.ident)) {
            self.add(Form::Bits64);
        }
        syn::visit::visit_expr_path(self, path);
    }
    // Macro arguments (`matches!`, `assert_eq!`) are tokens, not syntax.
    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        for _ in 0..bits64_in_tokens(mac.tokens.clone()) {
            self.add(Form::Bits64);
        }
        syn::visit::visit_macro(self, mac);
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

/// Whether a path ends in `LoadKind::Bits64`.
fn names_bits64<'a>(segments: impl Iterator<Item = &'a syn::Ident>) -> bool {
    let segments: Vec<_> = segments.collect();
    matches!(segments.as_slice(), [.., kind, variant] if *kind == "LoadKind" && *variant == "Bits64")
}

/// How many times `LoadKind::Bits64` is spelled in a macro's tokens.
fn bits64_in_tokens(tokens: proc_macro2::TokenStream) -> usize {
    let mut found = 0;
    let mut recent: Vec<String> = Vec::new();
    for token in tokens {
        match token {
            proc_macro2::TokenTree::Group(group) => {
                found += bits64_in_tokens(group.stream());
                recent.clear();
            }
            proc_macro2::TokenTree::Ident(ident) => {
                recent.push(ident.to_string());
                if recent.len() >= 4
                    && recent[recent.len() - 4..] == ["LoadKind", ":", ":", "Bits64"]
                {
                    found += 1;
                }
            }
            proc_macro2::TokenTree::Punct(punct) => recent.push(punct.as_char().to_string()),
            proc_macro2::TokenTree::Literal(_) => recent.clear(),
        }
    }
    found
}
