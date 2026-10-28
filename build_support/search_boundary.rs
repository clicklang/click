//! Build-time dependency checks for the incremental checking/search boundary.
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use syn::visit::Visit;

fn test_only(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|a| {
        a.path().is_ident("test")
            || (a.path().is_ident("cfg")
                && matches!(&a.meta, syn::Meta::List(m) if m.tokens.to_string() == "test"))
    })
}

// Failure diagnostics have narrowly reviewed entry points.
fn allowance(path: &str, function: &str, name: &str) -> usize {
    match (path, function, name) {
        ("src/kernel/assumptions.rs", "diagnostic_fact_sample", "diagnostic_fact_sample") => 1,
        (
            "src/kernel/api/contract_certification/contract_claims.rs",
            "unproved_contract_path_condition",
            "diagnostic_fact_sample",
        ) => 1,
        (
            "src/surface/proof/fixed_state_proofs/conversion_conditions.rs",
            "consulted_premises",
            "diagnostic_fact_sample",
        ) => 1,
        (
            "src/surface/proof/cursor_execution.rs",
            "listed_context_pure_facts",
            "diagnostic_fact_sample",
        ) => 1,
        _ => 0,
    }
}

struct Boundary<'a> {
    path: &'a str,
    function: String,
    counts: BTreeMap<(String, String), usize>,
    errors: Vec<String>,
}
impl Boundary<'_> {
    fn ident(&mut self, name: &str) {
        let name = name.strip_prefix("r#").unwrap_or(name);
        if self.path.starts_with("src/kernel/") && name == "PropositionSearch" {
            self.errors.push(format!(
                "{}: {}: checking must not depend on Surface planning ({name})",
                self.path, self.function
            ));
        }
        if matches!(name, "exact_pointer_aliases" | "pointer_spellings")
            && matches!(
                (self.path, self.function.as_str()),
                (
                    "src/kernel/assumptions.rs",
                    "memory_loadable_related_candidates"
                ) | (
                    "src/kernel/assumptions/memory_reasoning.rs",
                    "proves_memory_loadable_inner"
                )
            )
        {
            self.errors.push(format!(
                "{}: {}: checked view lookup must use indexed coordinates, not alias enumeration ({name})",
                self.path, self.function
            ));
        }
        if name == "memory_loadable_candidates" {
            self.errors.push(format!(
                "{}: {}: whole-block loadability enumeration is test-only; select a source in planning",
                self.path, self.function
            ));
        }
        if self.path.starts_with("src/kernel/")
            && name == "search_memory_loadable_candidates_for_base"
            && !(self.path == "src/kernel/assumptions.rs" && self.function == name)
        {
            self.errors.push(format!(
                "{}: {}: ambiguous loadability buckets require planning ({name})",
                self.path, self.function
            ));
        }
        if matches!(
            name,
            "without_exact_fact" | "forget_condition_fact" | "remove_proposition_fact"
        ) {
            self.errors.push(format!(
                "{}: {}: fact withdrawal is test-only; retain the parent context for branches ({name})",
                self.path, self.function
            ));
        }
        if self.path == "src/surface/proof/cursor_execution.rs"
            && self.function == "listed_context_pure_facts"
            && name == "pure_facts"
        {
            self.errors
                .push("step refusal must use the bounded diagnostic sampler".into());
        }
        if self.path == "src/surface/proof/fixed_state_proofs/conversion_conditions.rs"
            && matches!(
                name,
                "PropositionSearch" | "proves" | "derive_proposition" | "pure_facts"
            )
        {
            self.errors
                .push("conversion refusals must not search or scan the ambient context".into());
        }
        if matches!(name, "diagnostic_fact_sample") {
            *self
                .counts
                .entry((self.function.clone(), name.into()))
                .or_default() += 1;
        }
    }
    fn surface_dependency(&mut self) {
        if self.path.starts_with("src/kernel/") {
            self.errors.push(format!(
                "{}: {}: checking must not depend on Surface modules",
                self.path, self.function
            ));
        }
    }
    fn tokens(&mut self, tokens: proc_macro2::TokenStream) {
        for token in tokens {
            match token {
                proc_macro2::TokenTree::Ident(id) => {
                    if id == "surface" {
                        self.surface_dependency();
                    }
                    self.ident(&id.to_string());
                }
                proc_macro2::TokenTree::Group(group) => self.tokens(group.stream()),
                _ => (),
            }
        }
    }
}
impl<'ast> Visit<'ast> for Boundary<'_> {
    fn visit_item(&mut self, item: &'ast syn::Item) {
        let attrs: &[syn::Attribute] = match item {
            syn::Item::Mod(i) => &i.attrs,
            syn::Item::Fn(i) => &i.attrs,
            syn::Item::Impl(i) => &i.attrs,
            syn::Item::Use(i) => &i.attrs,
            syn::Item::Macro(i) => &i.attrs,
            _ => &[],
        };
        if !test_only(attrs) {
            syn::visit::visit_item(self, item);
        }
    }
    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        let previous = std::mem::replace(&mut self.function, item.sig.ident.to_string());
        syn::visit::visit_item_fn(self, item);
        self.function = previous;
    }
    fn visit_impl_item_fn(&mut self, item: &'ast syn::ImplItemFn) {
        if test_only(&item.attrs) {
            return;
        }
        let previous = std::mem::replace(&mut self.function, item.sig.ident.to_string());
        syn::visit::visit_impl_item_fn(self, item);
        self.function = previous;
    }
    fn visit_path(&mut self, path: &'ast syn::Path) {
        if path.segments.len() > 1 && path.segments.iter().any(|s| s.ident == "surface") {
            self.surface_dependency();
        }
        syn::visit::visit_path(self, path);
    }
    fn visit_use_path(&mut self, path: &'ast syn::UsePath) {
        if path.ident == "surface" {
            self.surface_dependency();
        }
        syn::visit::visit_use_path(self, path);
    }
    fn visit_use_name(&mut self, name: &'ast syn::UseName) {
        if name.ident == "surface" {
            self.surface_dependency();
        }
        syn::visit::visit_use_name(self, name);
    }
    fn visit_use_rename(&mut self, name: &'ast syn::UseRename) {
        if name.ident == "surface" {
            self.surface_dependency();
        }
        syn::visit::visit_use_rename(self, name);
    }
    fn visit_ident(&mut self, id: &'ast proc_macro2::Ident) {
        self.ident(&id.to_string());
    }
    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        self.visit_path(&mac.path);
        if self.path.starts_with("src/kernel/") && mac.path.is_ident("include") {
            self.errors.push(format!(
                "{}: use an audited module declaration instead of include! in checking",
                self.path
            ));
        }
        self.tokens(mac.tokens.clone());
    }
    // Documentation and cfg token text are not dependencies.
    fn visit_attribute(&mut self, _: &'ast syn::Attribute) {}
}

pub fn check_source(path: &str, source: &str) -> Result<syn::File, Vec<String>> {
    let file = syn::parse_file(source)
        .map_err(|e| vec![format!("{path}: cannot audit Rust source: {e}")])?;
    let mut boundary = Boundary {
        path,
        function: String::new(),
        counts: BTreeMap::new(),
        errors: Vec::new(),
    };
    boundary.visit_file(&file);
    for ((function, name), count) in &boundary.counts {
        let allowed = allowance(path, function, name);
        if *count > allowed {
            boundary.errors.push(format!("{path}: {function}: {name} has {count} references (reviewed allowance {allowed}); use indexed checking, explicit premises, or a capability-gated planner"));
        }
    }
    if boundary.errors.is_empty() {
        Ok(file)
    } else {
        Err(boundary.errors)
    }
}

fn external_modules(items: &[syn::Item], dir: &Path, result: &mut Vec<(PathBuf, PathBuf)>) {
    for item in items {
        let syn::Item::Mod(module) = item else {
            continue;
        };
        if test_only(&module.attrs) {
            continue;
        }
        let name = module.ident.to_string();
        if let Some((_, items)) = &module.content {
            external_modules(items, &dir.join(name), result);
        } else {
            let explicit = module.attrs.iter().find_map(|a| {
                if !a.path().is_ident("path") {
                    return None;
                }
                match &a.meta {
                    syn::Meta::NameValue(value) => match &value.value {
                        syn::Expr::Lit(syn::ExprLit {
                            lit: syn::Lit::Str(s),
                            ..
                        }) => Some(dir.join(s.value())),
                        _ => None,
                    },
                    _ => None,
                }
            });
            let path = explicit.unwrap_or_else(|| {
                let flat = dir.join(format!("{name}.rs"));
                if flat.exists() {
                    flat
                } else {
                    dir.join(&name).join("mod.rs")
                }
            });
            let children = if path.file_name().is_some_and(|n| n == "mod.rs") {
                path.parent().unwrap().to_path_buf()
            } else {
                path.with_extension("")
            };
            result.push((path, children));
        }
    }
}

/// Follow actual module declarations, including inline modules; test-only
/// modules are skipped by cfg, not by filename conventions.
pub fn check_tree(root: &Path, relative: &str) -> Result<(), Vec<String>> {
    let start = root.join(relative);
    let directory = if start.file_name().is_some_and(|name| name == "mod.rs") {
        start.parent().unwrap().to_path_buf()
    } else {
        start.with_extension("")
    };
    let mut pending = vec![(start.clone(), directory)];
    let mut errors = Vec::new();
    while let Some((path, dir)) = pending.pop() {
        println!("cargo:rerun-if-changed={}", path.display());
        let relative = path
            .strip_prefix(root)
            .unwrap()
            .to_string_lossy()
            .replace('\\', "/");
        let source =
            std::fs::read_to_string(&path).map_err(|e| vec![format!("{relative}: {e}")])?;
        match check_source(&relative, &source) {
            Ok(file) => external_modules(&file.items, &dir, &mut pending),
            Err(found) => errors.extend(found),
        }
    }
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}
