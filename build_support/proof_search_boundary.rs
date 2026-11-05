//! Exact migration inventory for proof-operation dependencies on discovery.
//! This is a source boundary, not a Rust complexity proof. Candidate-state
//! access and inline loops still require the operation audit.
use std::collections::BTreeMap;
use syn::visit::Visit;

pub const MANIFEST: &str = include_str!("proof_search_edges.tsv");
pub const DRIVER_METHODS: &str = include_str!("proof_driver_methods.txt");
pub const TARGETS: &str = include_str!("proof_search_targets.txt");

fn test_only(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|a| {
        a.path().is_ident("test")
            || (a.path().is_ident("cfg")
                && matches!(&a.meta, syn::Meta::List(m) if m.tokens.to_string() == "test"))
    })
}

#[derive(Default)]
struct Inventory {
    function: String,
    owner: String,
    edges: BTreeMap<(String, String, String), usize>,
    errors: Vec<String>,
}
impl Inventory {
    fn record(&mut self, target: &str) {
        if TARGETS.lines().any(|name| name == target) {
            *self
                .edges
                .entry((self.owner.clone(), self.function.clone(), target.to_owned()))
                .or_default() += 1;
        }
    }
    fn tokens(&mut self, tokens: proc_macro2::TokenStream) {
        for token in tokens {
            match token {
                proc_macro2::TokenTree::Ident(id) => self.record(&id.to_string()),
                proc_macro2::TokenTree::Group(group) => self.tokens(group.stream()),
                _ => (),
            }
        }
    }
}
impl<'ast> Visit<'ast> for Inventory {
    fn visit_item(&mut self, item: &'ast syn::Item) {
        let attrs = match item {
            syn::Item::Fn(i) => &i.attrs,
            syn::Item::Impl(i) => &i.attrs,
            syn::Item::Mod(i) => &i.attrs,
            syn::Item::Use(i) => &i.attrs,
            _ => return syn::visit::visit_item(self, item),
        };
        if !test_only(attrs) {
            syn::visit::visit_item(self, item);
        }
    }
    fn visit_item_impl(&mut self, item: &'ast syn::ItemImpl) {
        let previous = self.owner.clone();
        self.owner = match item.self_ty.as_ref() {
            syn::Type::Path(p) => p.path.segments.last().unwrap().ident.to_string(),
            _ => "impl".into(),
        };
        for i in &item.items {
            self.visit_impl_item(i);
        }
        self.owner = previous;
    }
    fn visit_impl_item_fn(&mut self, item: &'ast syn::ImplItemFn) {
        if test_only(&item.attrs) {
            return;
        }
        let name = item.sig.ident.to_string();
        if self.owner == "ProofDriver" && !DRIVER_METHODS.lines().any(|n| n == name) {
            self.errors
                .push(format!("unclassified ProofDriver entry point: {name}"));
        }
        if matches!(self.owner.as_str(), "Proof" | "ProofScope" | "ProofObject")
            && DRIVER_METHODS.lines().any(|n| n == name)
        {
            self.errors.push(format!(
                "driver method must not return to {}: {name}",
                self.owner
            ));
        }
        if self.owner == "ProofSearch" && !TARGETS.lines().any(|n| n == name) {
            self.errors
                .push(format!("unclassified ProofSearch entry point: {name}"));
        }
        if matches!(self.owner.as_str(), "Proof" | "ProofObject")
            && TARGETS.lines().any(|n| n == name)
        {
            self.errors.push(format!(
                "search method must not return to {}: {name}",
                self.owner
            ));
        }
        let previous = self.function.clone();
        self.function = name;
        self.visit_block(&item.block);
        self.function = previous;
    }
    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        if test_only(&item.attrs) {
            return;
        }
        let previous = self.function.clone();
        self.function = if previous.is_empty() {
            item.sig.ident.to_string()
        } else {
            format!("{previous}/{}", item.sig.ident)
        };
        self.visit_block(&item.block);
        self.function = previous;
    }
    fn visit_expr_method_call(&mut self, call: &'ast syn::ExprMethodCall) {
        self.record(&call.method.to_string());
        syn::visit::visit_expr_method_call(self, call);
    }
    fn visit_expr_path(&mut self, expr: &'ast syn::ExprPath) {
        if let Some(last) = expr.path.segments.last() {
            // Local closures named `proves` are not the search interface.
            if expr.path.segments.len() != 1 || last.ident != "proves" {
                self.record(&last.ident.to_string());
            }
        }
        syn::visit::visit_expr_path(self, expr);
    }
    fn visit_use_name(&mut self, name: &'ast syn::UseName) {
        self.record(&name.ident.to_string());
    }
    fn visit_use_rename(&mut self, name: &'ast syn::UseRename) {
        self.record(&name.ident.to_string());
    }
    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        self.tokens(mac.tokens.clone());
    }
    fn visit_attribute(&mut self, _: &'ast syn::Attribute) {}
}

pub fn inventory(path: &str, file: &syn::File) -> BTreeMap<String, usize> {
    let mut visitor = Inventory::default();
    visitor.visit_file(file);
    visitor
        .edges
        .into_iter()
        .map(|((owner, caller, target), count)| {
            // Reviewed roles describe callers, not a transitive complexity proof.
            let role = if caller.is_empty() {
                "import"
            } else if owner == "ProofDriver"
                && target != "driver"
                && matches!(
                    caller.as_str(),
                    "apply_step_without_outcome_wrapping" | "apply_theorem_application"
                )
            {
                // Moving explicit tactic dispatch must not relabel its search
                // dependencies as legitimate implicit closing.
                "operation"
            } else if owner == "ProofDriver" || path.starts_with("src/surface/proof/driver/") {
                "driver"
            } else if owner == "ProofSearch"
                || path.starts_with("src/kernel/search")
                || path.starts_with("src/surface/planning/")
            {
                "search"
            } else if path.starts_with("src/kernel/") {
                if matches!(
                    target.as_str(),
                    "loan_aliases"
                        | "loan_access"
                        | "ownership_validity_candidates"
                        | "ownership_overlap"
                        | "owned_anchor_distinctness"
                        | "composition_context"
                        | "call_frame"
                ) {
                    "legacy-bridge"
                } else {
                    "legacy-caller"
                }
            } else if target == "driver" && matches!(owner.as_str(), "Proof" | "ProofScope") {
                "operation-to-driver"
            } else if owner == "ProofScope" {
                "scope-adapter"
            } else if matches!(
                caller.as_str(),
                "spelled_goal"
                    | "structural_proposition_candidate"
                    | "record_spellability_census"
                    | "trace_pointer_pair"
                    | "spell_refutation"
                    | "spelled_goal_for_search"
                    | "unsigned_surface_fact"
            ) {
                "presentation"
            } else if matches!(
                caller.as_str(),
                "apply_planned_fact_transport_inner"
                    | "apply_planned_outcome_fact_transport"
                    | "apply_pure_transport_using"
                    | "apply_step_without_outcome_wrapping"
                    | "apply_theorem_application"
                    | "certified_fact_transport_reaches"
                    | "check_fixed_state_fact_transport_using_facts_inner"
                    | "certified_transitions_from_execution"
                    | "capture_resource_field_initializer"
                    | "surface_branch_path_for_outcome"
                    | "symbolic_segment_covers_index"
                    | "symbolic_segment_covers_range"
            ) {
                "operation"
            } else if matches!(
                caller.as_str(),
                "apply_frontier_source_tactic"
                    | "run_addressed_linear_script"
                    | "solve_nested_have"
                    | "close_post_execution_claims_with_solve"
                    | "close_bundle_member_by_solve"
                    | "preservation_smart_step"
            ) {
                "dispatch"
            } else {
                // Mixed drivers and auxiliary planners need caller-level audit.
                "mixed"
            };
            (
                format!("{path}\t{role}\t{owner}::{caller}\t{target}"),
                count,
            )
        })
        .collect()
}

pub fn expected() -> BTreeMap<String, usize> {
    MANIFEST
        .lines()
        .filter(|line| !line.starts_with('#') && !line.is_empty())
        .map(|line| {
            let (key, count) = line.rsplit_once('\t').expect("dependency record count");
            (
                key.to_owned(),
                count.parse().expect("dependency reference count"),
            )
        })
        .collect()
}

pub fn check(path: &str, file: &syn::File) -> Result<(), Vec<String>> {
    let expected = expected();
    let mut definitions = Inventory::default();
    definitions.visit_file(file);
    let mut errors = definitions.errors;
    let actual = inventory(path, file);
    for (key, count) in &actual {
        if expected.get(key).copied().unwrap_or(0) != *count {
            errors.push(format!("unreviewed proof-search dependency: {key} ({count} references); preserve the frozen inventory or explicitly review this boundary change"));
        }
    }
    for key in expected.keys() {
        if key.split('\t').next() == Some(path) && !actual.contains_key(key) {
            errors.push(format!("stale proof-search dependency: {key}; remove the reviewed record when deleting or relocating this edge"));
        }
    }
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}
