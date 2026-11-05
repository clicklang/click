//! Build-time dependency checks for the incremental checking/search boundary.
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use syn::visit::Visit;
#[path = "proof_search_boundary.rs"]
mod proof_search_boundary;

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
        if self.path == "src/kernel/loans.rs"
            && self.function == "has_active_memory_loans"
            && matches!(
                name,
                "iter"
                    | "values"
                    | "keys"
                    | "collect"
                    | "any"
                    | "all"
                    | "fold"
                    | "count"
                    | "loans"
                    | "scopes"
                    | "unindexed_memory"
                    | "active_memory_index"
                    | "cache_memory_index"
                    | "loan_protects_memory"
            )
        {
            self.errors.push(format!(
                "{}: {}: memory-loan presence must read the maintained count ({name})",
                self.path, self.function
            ));
        }
        if self.path == "src/kernel/loans.rs"
            && matches!(
                self.function.as_str(),
                "permits_memory_access_with_assumptions"
                    | "conflicting_memory_loan"
                    | "first_active_memory_overlap"
                    | "first_active_memory_overlap_with_assumptions"
            )
            && matches!(
                name,
                "active_memory_overlaps" | "active_memory_overlaps_with_assumptions"
            )
        {
            self.errors.push(format!(
                "{}: {}: write checks must select a conflict witness, not collect loans ({name})",
                self.path, self.function
            ));
        }
        if self.path == "src/kernel/loans.rs"
            && matches!(
                self.function.as_str(),
                "first_active_memory_overlap" | "first_active_memory_overlap_with_assumptions"
            )
            && matches!(
                name,
                "collect"
                    | "with_value"
                    | "flat_map"
                    | "filter"
                    | "find"
                    | "find_map"
                    | "for_each"
                    | "fold"
            )
        {
            self.errors.push(format!(
                "{}: {}: indexed conflict selection must not enumerate loan buckets ({name})",
                self.path, self.function
            ));
        }
        if self.path == "src/kernel/primitives/memory_state.rs"
            && matches!(
                self.function.as_str(),
                "loan_preserving_havoc_keeps_cell" | "loan_preserving_havoc_keeps_run"
            )
            && matches!(
                name,
                "permits_memory_access"
                    | "permits_memory_access_with_assumptions"
                    | "active_memory_overlaps"
            )
        {
            self.errors.push(format!(
                "{}: {}: cache retention must not search loan protection ({name})",
                self.path, self.function
            ));
        }
        if self.path == "src/kernel/loans.rs"
            && self.function == "has_indexed_memory_overlap"
            && matches!(
                name,
                "iter"
                    | "collect"
                    | "unindexed_memory"
                    | "permits_memory_access"
                    | "permits_memory_access_with_assumptions"
                    | "active_memory_overlaps"
                    | "protected_range_proven_overlapping"
            )
        {
            self.errors.push(format!(
                "{}: {}: cache protection must use interval bucket occupancy ({name})",
                self.path, self.function
            ));
        }
        if self.path == "src/kernel/primitives/resource_algebra.rs"
            && self.function == "constant_memory_overlap"
            && matches!(
                name,
                "iter"
                    | "collect"
                    | "find"
                    | "find_map"
                    | "filter"
                    | "flat_map"
                    | "for_each"
                    | "exact_pointer_aliases"
                    | "exact_pointer_offset_aliases"
                    | "memory_ranges_proven_overlapping"
                    | "memory_ranges_proven_overlapping_without_aliases"
                    | "facts"
            )
        {
            self.errors.push(format!(
                "{}: {}: constant overlap must compare explicit byte coordinates ({name})",
                self.path, self.function
            ));
        }
        if self.path == "src/kernel/primitives/resource_algebra.rs"
            && self.function == "has_owned_memory_outside_block"
            && matches!(
                name,
                "iter"
                    | "collect"
                    | "find"
                    | "find_map"
                    | "filter"
                    | "flat_map"
                    | "for_each"
                    | "exact_pointer_aliases"
                    | "exact_pointer_offset_aliases"
                    | "owned_validity_candidates"
                    | "facts"
            )
        {
            self.errors.push(format!(
                "{}: {}: owner absence must use cached block counts ({name})",
                self.path, self.function
            ));
        }
        if self.path == "src/kernel/primitives/resource_algebra.rs"
            && self.function == "owned_validity_candidates"
            && matches!(name, "memory_by_base" | "memory_by_block")
        {
            self.errors.push(format!(
                "{}: {}: ownership validity must select owner-only buckets ({name})",
                self.path, self.function
            ));
        }
        if self.path == "src/kernel/loans.rs"
            && matches!(
                name,
                "has_other_directly_supporting_owned_entry"
                    | "changed_facts_since"
                    | "descends_from"
            )
        {
            self.errors.push(format!("{}: {}: loan provenance must retain split origins, not reconstruct them by search or history ({name})", self.path, self.function));
        }
        if self.path == "src/kernel/loans.rs"
            && (name == "view_occurrences_for_fact"
                || name == "with_coalesced_owned_memory"
                || (matches!(
                    self.function.as_str(),
                    "bound_view_candidate" | "select_bound_view"
                ) && matches!(
                    name,
                    "find" | "find_map" | "filter" | "filter_map" | "collect"
                )))
        {
            self.errors.push(format!("{}: {}: loan binding selection must nominate an indexed identity, not scan observations ({name})", self.path, self.function));
        }
        if ((self.path == "src/kernel/loops.rs" && self.function == "loop_body_resource_context")
            || (self.path == "src/kernel/loans.rs" && self.function == "attach_to_inserted_views"))
            && (matches!(name, "view_occurrences_for_fact" | "find" | "find_map")
                || (self.function == "attach_to_inserted_views" && name == "facts"))
        {
            self.errors.push(format!("{}: {}: loop binding handoff must retain producer occurrences, not rediscover views ({name})", self.path, self.function));
        }
        if ((self.path == "src/kernel/loans.rs" && self.function == "recover_stable_views_impl")
            || (self.path == "src/kernel/functions.rs"
                && matches!(
                    self.function.as_str(),
                    "recover_candidate_stable_view_resources"
                        | "evaluate_contract_return_resources"
                )))
            && (matches!(
                name,
                "normalized_around_facts"
                    | "try_compose_with_fact_with_occurrence"
                    | "try_compose_with_facts_delaying_normalization"
                    | "try_compose_with_facts_delaying_normalization_with_occurrences"
            ) || (self.function == "recover_candidate_stable_view_resources"
                && name == "facts"))
        {
            self.errors.push(format!(
                "{}: {}: call completion must insert the recorded delta without scanning or normalizing the caller frame ({name})",
                self.path, self.function
            ));
        }
        if self.path == "src/kernel/loops.rs"
            && self.function == "with_loop_frame_resources"
            && matches!(name, "owned_memory_facts" | "memory_facts_in_block")
        {
            self.errors.push(format!("{}: {}: explicit loop frames must select scalar blocks and their owned occurrences ({name})", self.path, self.function));
        }
        if self.path == "src/kernel/primitives/resource_algebra.rs"
            && self.function == "has_no_explicit_memory_for_local_storage"
            && matches!(
                name,
                "iter"
                    | "collect"
                    | "find"
                    | "find_map"
                    | "memory_fact_candidates"
                    | "view_occurrences_for_fact"
            )
        {
            self.errors.push(format!(
                "{}: {}: local-storage classification must use indexed absence evidence ({name})",
                self.path, self.function
            ));
        }
        if self.path == "src/kernel/primitives/resource_algebra.rs"
            && self.function == "constant_owned_neighbors"
            && matches!(
                name,
                "collect"
                    | "find"
                    | "find_map"
                    | "filter"
                    | "flat_map"
                    | "for_each"
                    | "owned_validity_candidates"
                    | "memory_fact_candidates"
                    | "normalized_memory_suppliers"
                    | "facts"
            )
        {
            self.errors.push(format!(
                "{}: {}: owner neighbours must use fixed tree/end probes ({name})",
                self.path, self.function
            ));
        }
        if self.path == "src/kernel/functions.rs" && name == "with_coalesced_owned_memory" {
            self.errors.push(format!(
                "{}: {}: call preparation must not search fragment coverage",
                self.path, self.function
            ));
        }
        if self.path == "src/kernel/primitives/resource_algebra.rs"
            && matches!(
                self.function.as_str(),
                "directly_supporting_memory_fact"
                    | "constant_relative_byte_endpoints"
                    | "constant_memory_coordinates"
                    | "constant_owned_neighbors_at_exact_alias"
                    | "consume_unit_owned_memory"
                    | "consume_symbolic_partition"
                    | "memory_range_definitely_shorter"
                    | "reserve_owned_memory_fragments_impl"
            )
            && matches!(
                name,
                "iter"
                    | "collect"
                    | "find"
                    | "find_map"
                    | "normalized_memory_suppliers"
                    | "with_coalesced_owned_memory"
            )
        {
            self.errors.push(format!(
                "{}: {}: memory support must use indexed suppliers ({name})",
                self.path, self.function
            ));
        }
        if self.path == "src/kernel/primitives/resource_algebra.rs"
            && matches!(
                self.function.as_str(),
                "without_selected_fact_with_origins"
                    | "has_indexed_view_witness"
                    | "indexed_view_witness"
            )
            && matches!(
                name,
                "iter"
                    | "find"
                    | "find_map"
                    | "collect"
                    | "normalized_memory_suppliers"
                    | "without_fact_incrementally"
            )
        {
            self.errors.push(format!(
                "{}: {}: selected consumption must use the supplied occurrence ({name})",
                self.path, self.function
            ));
        }
        if self.path == "src/kernel/primitives/resource_algebra.rs"
            && self.function == "origin_of"
            && matches!(
                name,
                "iter" | "find" | "find_map" | "filter" | "filter_map" | "collect"
            )
        {
            self.errors.push(format!(
                "{}: {}: split origin lookup must read a direct identity ({name})",
                self.path, self.function
            ));
        }
        if self.path == "src/kernel/primitives/resource_algebra.rs"
            && self.function == "direct_nonmemory_support_entry"
            && matches!(
                name,
                "find"
                    | "find_map"
                    | "filter"
                    | "filter_map"
                    | "flat_map"
                    | "collect"
                    | "direct_match_candidates_for"
                    | "related_pointer_roots"
            )
        {
            self.errors.push(format!("{}: {}: owned support must select an indexed witness, not search a candidate bucket ({name})", self.path, self.function));
        }
        if self.path == "src/kernel/primitives/resource_algebra.rs"
            && self.function == "directly_supporting_owned_entry_with_separation"
            && matches!(
                name,
                "iter" | "find" | "find_map" | "filter" | "filter_map" | "flat_map" | "collect"
            )
        {
            self.errors.push(format!("{}: {}: single-owner support must select one supplier, not enumerate fragments ({name})", self.path, self.function));
        }
        if self.path == "src/kernel/primitives/memory_equality_index.rs"
            && self.function == "single_supplier"
            && matches!(
                name,
                "signed_order_bound_entries"
                    | "get_greater_than"
                    | "find"
                    | "find_map"
                    | "filter"
                    | "filter_map"
                    | "flat_map"
                    | "collect"
            )
        {
            self.errors.push(format!("{}: {}: whole-range supplier selection must not search a fragment or premise frontier ({name})", self.path, self.function));
        }
        if self.path.starts_with("src/kernel/") && name == "PropositionSearch" {
            self.errors.push(format!(
                "{}: {}: checking must not depend on Surface planning ({name})",
                self.path, self.function
            ));
        }
        if (self.path == "src/kernel/equality_graph/evidence.rs"
            && self.function == "direct_scalar_constant"
            && matches!(
                name,
                "scalar_evidence_inputs" | "scalar_evidence_class" | "scalar_evidence_derivation"
            ))
            || (self.path == "src/kernel/assumptions/memory_reasoning.rs"
                && matches!(
                    self.function.as_str(),
                    "written_base_spellings"
                        | "owned_store_footprint"
                        | "access_owned_apart_from_store"
                )
                && matches!(
                    name,
                    "pointer_alias_class"
                        | "exact_pointer_aliases"
                        | "base_spellings_through_aliases"
                ))
        {
            self.errors.push(format!("{}: {}: direct checking must use written equality/address premises, not discover alias paths ({name})", self.path, self.function));
        }
        if self.path == "src/kernel/assumptions/memory_reasoning.rs"
            && matches!(
                self.function.as_str(),
                "owned_store_footprint"
                    | "store_members_in"
                    | "access_owned_apart_from_store"
                    | "parameter_store_partition"
                    | "parameter_partition_cell_base"
            )
            && matches!(
                name,
                "owned_memory_members_with_base"
                    | "memory_members_with_base"
                    | "owned_member_holding_access"
                    | "listed_under"
                    | "listed_under_members"
                    | "listed_under_anchors"
            )
        {
            self.errors.push(format!("{}: {}: automatic store ownership must select singleton buckets, not enumerate members or compositions ({name})", self.path, self.function));
        }
        if self.path == "src/kernel/primitives/memory_state.rs"
            && self.function == "without_possible_aliasing_cells"
            && matches!(
                name,
                "owned_composition_store_separated_evidence"
                    | "owned_composition_store_separated_evidence_impl"
                    | "pointers_proven_disjoint_by_explicit_range_for_memory_resolution"
                    | "pointers_directly_disjoint_by_range"
                    | "pointers_proven_distinct_for_memory_resolution"
            )
        {
            self.errors.push(format!("{}: {}: store preservation must not retry general composition or range search ({name}); supply separation and transport explicitly", self.path, self.function));
        }
        if self.path == "src/kernel/reasoning/memory_resolution.rs"
            && ((self.function == "one_element_gap_separates_bytes"
                && matches!(
                    name,
                    "proves_recorded_signed_order" | "decide" | "signed_order_bound_entries"
                ))
                || (matches!(
                    self.function.as_str(),
                    "run_slots_kept_by_store" | "run_has_direct_store_separation"
                ) && matches!(
                    name,
                    "typed_ranges_disjoint_from_pointer_evidence"
                        | "typed_range_disjoint_from_pointer_evidence"
                        | "PerSlot"
                        | "AskWithin"
                )))
        {
            self.errors.push(format!("{}: {}: automatic store geometry requires direct facts and compact interval decisions ({name})", self.path, self.function));
        }
        if self.path == "src/kernel/reasoning/memory_resolution.rs"
            && self.function == "pointers_directly_distinct_for_store"
            && matches!(
                name,
                "pointers_proven_distinct_for_memory_resolution"
                    | "pointers_proven_distinct_for_memory_resolution_unmemoized"
                    | "pointer_offsets_equal_for_memory_resolution"
                    | "pointer_offsets_with_common_base_proven_distinct_for_memory_resolution"
                    | "pointers_proven_disjoint_by_explicit_range_for_memory_resolution"
                    | "exact_pointer_aliases"
                    | "proves_recorded_signed_order"
                    | "decide"
            )
        {
            self.errors.push(format!(
                "{}: {}: store distinctness must use direct evidence, not general search ({name})",
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
                        | "has_memory_read_defined_evidence"
                        | "kept_memory_range_holding_access"
                )
            )
        {
            self.errors.push(format!(
                "{}: {}: checked view lookup must use indexed coordinates, not alias enumeration ({name})",
                self.path, self.function
            ));
        }
        if matches!(
            name,
            "bitvector_equality_class"
                | "scalar_evidence_class"
                | "exact_offset_aliases"
                | "condition_match_keys_for_spellings"
        ) && matches!(
            (self.path, self.function.as_str()),
            (
                "src/kernel/assumptions/condition_reasoning/decision.rs",
                "has_condition_fact" | "decide_by_equivalent_order"
            ) | (
                "src/kernel/assumptions/condition_reasoning/selected_conditions.rs",
                "indexed_matching_condition_fact_for_memory_resolution"
            )
        ) {
            self.errors.push(format!("{}: {}: checked conditions must use indexed truth or selected premises, not alias enumeration ({name})", self.path, self.function));
        }
        if self.path == "src/kernel/assumptions/memory_reasoning.rs"
            && self.function == "kept_memory_range_holding_access"
            && matches!(
                name,
                "owned_memory_members_in_block"
                    | "memory_members_with_base"
                    | "kept_range_bases_proven_equal"
            )
        {
            self.errors.push(format!(
                "{}: {}: kept-frame fallback requires indexed selection ({name})",
                self.path, self.function
            ));
        }
        if self.path == "src/kernel/assumptions.rs"
            && ((matches!(
                self.function.as_str(),
                "designations_equal" | "opaque_extents_equal"
            ) && name == "direct_aliases")
                || (self.function == "known_value_of_framed_pointer_read"
                    && name == "exact_pointer_aliases"))
        {
            self.errors.push(format!("{}: {}: checked provenance requires indexed equality or a singleton source ({name})", self.path, self.function));
        }
        if self.path.starts_with("src/kernel/") && name == "condition_facts_with_side" {
            self.errors.push(format!("{}: {}: checked equality/order queries require indexed summaries or selected witnesses ({name})", self.path, self.function));
        }
        if self.path == "src/kernel/assumptions/condition_reasoning/overflow_intervals.rs"
            && matches!(
                name,
                "upper_bounds_for_search"
                    | "lower_bounds_for_search"
                    | "chained_signed_constant_bound"
                    | "exact_signed_order_bounds"
                    | "exact_signed_order_bounds_for_key"
            )
        {
            self.errors.push(format!(
                "{}: {}: checked intervals cannot enumerate symbolic order components ({name})",
                self.path, self.function
            ));
        }
        if self.path == "src/kernel/assumptions/condition_reasoning/decision.rs"
            && matches!(
                self.function.as_str(),
                "signed_constant_evidence" | "indexed_exact_int32_constant"
            )
            && matches!(name, "signed_order_bound_entries" | "exact_literal_sources")
        {
            self.errors.push(format!("{}: {}: constant equality evidence requires selected extrema or a singleton source ({name})", self.path, self.function));
        }
        if self.path == "src/kernel/primitives/resource_algebra.rs"
            && matches!(
                name,
                "MemoryAccessCandidates" | "access_entries" | "indexed_access_entries"
            )
        {
            self.errors.push(format!("{}: {}: checked access requires one SelectedMemoryAccess, not candidate enumeration ({name})", self.path, self.function));
        }
        if name == "memory_loadable_candidates" {
            self.errors.push(format!(
                "{}: {}: whole-block loadability enumeration is test-only; select a source in planning",
                self.path, self.function
            ));
        }
        if self.path.starts_with("src/kernel/")
            && !self.path.starts_with("src/kernel/search/")
            && matches!(
                name,
                "search_memory_loadable_candidates_for_base"
                    | "search_memory_read_defined_candidates"
            )
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
            Ok(file) => {
                if let Err(found) = proof_search_boundary::check(&relative, &file) {
                    errors.extend(found);
                }
                external_modules(&file.items, &dir, &mut pending);
            }
            Err(found) => errors.extend(found),
        }
    }
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}
