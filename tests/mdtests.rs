use click::surface::ProgramInputs;
use std::fs;
use std::path::{Path, PathBuf};

use cpp_imports::{checked_in_files, first_import_difference, same_import};

use click::cli::{
    MdTestExpectation, VerificationInput, export_cpp_mdtest_import, prepare_mdtest_inputs,
    read_click_project, read_mdtest, read_mdtest_project_if_needed,
    read_verification_inputs_for_project, source_refs,
};
use click::instrumentation::{self, HiddenPrerequisiteRoute};
use click::surface::{
    ClickError, c_tactic_source_position, project_tactic_source_position, verify_c_project,
    verify_c_sources, verify_program_prepared_project,
};

#[path = "support/cpp_imports.rs"]
mod cpp_imports;
#[path = "support/limits.rs"]
mod limits;
#[path = "support/quick_solve.rs"]
mod quick_solve;
#[path = "support/tactic_work.rs"]
mod tactic_work;

const RUN_QUARANTINED: &str = "CLICK_RUN_QUARANTINED";
/// Rewrites the checked-in C++ imports instead of comparing them.
const REFRESH_CPP_IMPORTS: &str = "CLICK_REFRESH_CPP_IMPORTS";
const QUICK_SOLVE_ONLY: &str = "MDTEST_QUICK_SOLVE";
const BUBBLE_SORT3_WORK_LIMIT: usize = 100_000;
/// Pin the explicit frame refusal under a fixed work limit.
const PROMPT_EXPLICIT_FRAME_FAILURE_WORK_LIMIT: usize = 250_000;

/// Known-broken mdtests, skipped by default so the suite is a meaningful
/// green gate. Run one with `MDTEST_FILTER=<name>`, or all of them with
/// `CLICK_RUN_QUARANTINED=1`. Each entry names the reason; remove entries as
/// they are fixed (see docs/internals/testing.md).
const QUARANTINED: &[(&str, &str)] = &[];

/// Mdtests the ten-minute gate leaves to the nightly run
/// (`scripts/check.sh --nightly`), with the time each took in the parallel
/// gate on four cores (2026-10-13, and 2026-11-25 for the last block). The gate runs a fixture only if it takes
/// under half a second (`docs/internals/testing.md`). Shared `.click` lemma
/// libraries stay in the gate so it checks both sides of their imports. Run
/// one with `MDTEST_FILTER=<name>`.
const NIGHTLY: &[&str] = &[
    // 8.85s in the parallel gate. The kernel test a_store_inside_the_range_is_refused
    // checks the overlapping store directly. Nightly also checks solve's refusal.
    "fold_read_transport_rejects_a_store_inside_the_range.md",
    "c_function_type_typedef.md", // 0.86s focused: verify callback dispatch through an alias parameter and a field
    "pointer_offset_explicit_bridge.md", // 0.81s focused: explicit scalar-pointer law applications
    "nested_conditional_explicit_arm_equations.md", // 0.89s focused: arithmetic, observations and casts
    "widened_unsigned_sum_returned_identity.md",    // 1.19s focused: explicit returned-sum identity
    "widened_unsigned_sum_observation_identity.md", // 0.63s focused: widening and reassociation
    "aligned_address_word_library.md", // 0.9s focused: 36 explicit word and scalar-pointer law applications
    "loop_numeric_descent_on_exit.md", // 1.09s focused: split final and continuing preservation paths
    "loop_numeric_descent_on_generated_exit.md", // 0.58s in parallel: generated preservation of a false next test
    "a_returned_member_domain_supports_a_logical_read.md", // 2.3s: member-result resource fold and logical read
    "scalar_induction_after_helper_facts.md", // 0.78s in the parallel induction fixture selection
    "witness_mixed_type_values.md", // 1.36s focused: pointer, Integer, and machine binders
    "modeled_pthread_copied_handle.md", // 0.6s focused: forwarded handle and retained equality
    "modeled_pthread_copied_handle_join_twice.md", // forwarded handle must consume one right
    "shared_loop_test_and_update.md", // 1.2s focused: ranked pre/post-test call proofs
    "shared_loop_post_test_ends_body_scope.md", // 0.8s focused: post-test after an expired body array
    "a_summarized_pure_loop_does_not_record_its_test_state.md", // 0.84s focused; fast layout coverage checks the test selector
    "a_fixed_range_transfer_preserves_the_retained_tail.md", // 0.55s focused: typed byte-range call and return
    "consumed_scalar_transfer_mixes_with_a_borrowed_return.md", // 0.67s focused: two-parameter call and caller return
    "aliased_packaged_views_keep_their_selected_whole_borrow.md", // 0.71s focused: selected whole-borrow recovery
    "multiple_witnesses_survive_checked_calls.md", // 1.07s focused: repeated calls with two recorded witnesses
    "symbolic_return_boundary_uses_explicit_bounds.md", // 0.78s focused: symbolic return beside retained memory
    "symbolic_output_partitions_rejoin_a_retained_frame.md", // 3.8s focused: symbolic flat/composite partitions beside retained memory
    "integer_migration_routes.md", // 0.9s: signed/native routes and rounding
    "aggregate_expression_results_are_named_by_their_source_steps.md", // 1.61s focused
    "aggregate_result_storage_ends_at_the_statement_exit.md", // 0.82s focused in parallel
    // 0.78s focused, 0.57s in the parallel gate; the automatic-array refusal
    // below has the same store-search miss line.
    "a_store_search_miss_names_the_store_and_the_fact_for_a_heap_read.md",
    // 0.79s focused, 0.63s in the corpus (2026-11-12): once `j != 1` made
    // `1 <= j` strict, the honest miss needs `j` free to be 1 and a claim
    // that holds only by a case split, which the failing tail searches;
    // `a_store_index_bound_and_disequality_keep_a_cached_element.md` keeps
    // the store search's hit in the gate.
    "a_store_search_miss_names_the_store_and_the_fact_for_an_array_read.md",
    // 0.74s focused; the `int32` array-read miss stays in the gate.
    "a_size_t_store_search_miss_names_the_word_fact.md",
    // 0.86s focused; `a_stated_store_search_fact_keeps_the_heap_cell.md`
    // keeps a stated store-search fact in the gate.
    "a_stated_size_t_store_search_fact_keeps_the_heap_cell.md",
    // 0.88s focused; `a_size_t_store_at_an_index_that_may_be_the_cached_one_overwrites_it.md`
    // keeps a `size_t` store refusal in the gate.
    "a_wrapping_size_t_store_index_overwrites_the_cached_element.md",
    // 0.81s focused; `a_store_at_the_last_size_t_heap_element_keeps_the_first.md`
    // keeps a `size_t` store search hit in the gate.
    "a_size_t_store_index_fact_variants_keep_the_first.md",
    // 0.62s focused; `solve_proves_element_addresses_distinct_from_their_indices.md`
    // keeps the element-address strategy in the gate.
    "solve_proves_element_addresses_distinct_at_each_index_type.md",
    // 0.75s focused; nested-read identity and the positive C case stay in the gate.
    "nested_index_read_does_not_use_the_changed_index.md",
    "a_decreases_measure_sum_is_an_integer.md", // 2.4s: original disjunctive-guard regression
    // Eleven sequential branches exhaust the loop closer's work budget.
    // `an_automatically_closed_loop_splits_at_its_c_branches.md`
    // keeps the smaller loop-body splitting case in the gate.
    "a_branching_loop_stops_at_the_work_limit.md",
    // 1.9s focused; retain the full stack-pop case alongside the isolated
    // constructor-guard scaling regression.
    "refuted_implication_after_stack_pop.md",
    // 2.60s in its focused harness run; the unit regression stays in the gate.
    "equal_object_origins_frame_neighbor_fields.md",
    // 1.7s; `Stack<int>::pop` stays in the gate in `examples/cpp-stack`, and
    // the abstract-value unit regressions in `memory_dag_tests` stay too.
    "cpp_generic_resource_checked_once.md",
    // 6.9s; a proof naming object state stays in the gate in
    // `cpp_class_template_override_calls_its_own_method.md`.
    "cpp_class_object_state_named_in_a_proof.md",
    // 17s; an override calling a method that states its own resource stays
    // in the gate in `cpp_class_resource_state_override_calls_a_helper.md`.
    "cpp_generic_stack_is_a_container.md",
    "a_bounded_symbolic_read_of_an_initialized_local_array_is_initialized.md", // 0.6s
    "a_frame_holds_across_a_write_at_a_64_bit_index.md",                       // 0.7s
    "a_freed_cell_is_not_read_through_another_owner_after_a_loop.md",          // 1.2s
    "a_pointer_saved_before_a_loop_is_not_read_through_the_owner_after_it.md", // 1.0s
    "a_read_back_across_a_store_that_misses_its_cell_is_the_earlier_store.md", // 0.5s
    "a_store_at_a_bounded_index_inside_an_owned_array_parameter_is_authorized.md", // 0.9s
    "a_store_below_an_owned_global_range_is_refused.md",                       // 0.6s
    "a_store_inside_the_copy_does_not_keep_copied_bytes.md",                   // 0.8s
    "a_table_of_three_named_callback_contracts_calls_one.md",                  // 0.5s
    "a_wide_store_after_a_root_call_is_not_the_old_tag.md",                    // 0.6s
    "abutting_contract_ranges_keep_each_clause_at_certification.md",           // 0.7s
    "aggregate_static_objects.md",                                             // 0.7s
    "augment_rotate_callback.md",                                              // 3.5s
    "augment_rotate_callback_rejects_consumed_shape.md",                       // 3.1s
    "augment_rotate_callback_rejects_extra_write.md",                          // 2.9s
    "augment_rotate_model_callback_rejects_relink.md",                         // 1.8s
    "authority_certifies_observed_child_views.md",                             // 1.4s
    "authority_exact_symbolic_population_total.md",                            // 0.5s
    "authority_four_effect_exchange.md",                                       // 0.6s
    "authority_ordinary_exit_refolds_a_consumed_family.md",                    // 2.0s
    "authority_pool_checkout_helper_without_slot_rejected.md",                 // 0.6s
    "authority_pool_cleanup_field_quantity.md",                                // 0.8s
    "authority_pool_control_two_members.md",                                   // 4.0s
    "authority_pool_private_body_alias_birth.md",                              // 0.7s
    "authority_symbolic_batch_cleanup_helper.md",                              // 0.7s
    "authority_two_control_birth_helpers.md",                                  // 1.6s
    "authority_wildcard_contained_resource.md",                                // 0.8s
    "authority_wildcard_transfer_private_body.md",                             // 0.5s
    "solve_proves_a_conservation_equation.md",                                 // 2.5s
    "borrowing_composite_survives_an_owning_call.md",                          // 2.3s
    "branch_interface_keeps_model_pointer_names.md",                           // 0.8s
    "branch_interface_rejects_changed_aliased_wide_word.md",                   // 1.0s
    "branching_graph_dfs.md",                                                  // 6.2s
    "bubble_pass3_max_suffix.md",                                              // 0.9s
    "bubble_sort3_loop_permutation.md",                                        // 1.3s
    "bubble_sort3_loop_sorted.md",                                             // 0.6s
    "bubble_sort3_two_pass_sorted.md",                                         // 0.9s
    "byte_count_of_two_merged_branches_matches_the_c_count.md",                // 1.2s
    "c_buffer_resource_modular_output.md",                                     // 0.5s
    "c_chained_field_access.md",                                               // 1.1s
    "c_contract_executes_status.md",                                           // 0.6s
    "c_contract_executes_status_nested.md",                                    // 0.9s
    "c_decreases_matched_arm_child.md",                                        // 0.8s
    "c_decreases_resource_recursive_in_loop.md",                               // 0.5s
    "c_decreases_resource_recursive_in_loop_rejects_parent.md",                // 0.5s
    "c_decreases_resource_rejects_unrelated.md",                               // 0.6s
    "c_decreases_resource_tree_child.md",                                      // 1.0s
    "c_named_function_contract_accepts_symbolic_mutable_subrange.md",          // 0.6s
    "c_named_function_contract_frames_guarded_composite.md",                   // 0.8s
    "c_named_function_contract_refinement_theorem.md",                         // 0.7s
    "c_pointer_field_preserving_calls_join_branches.md",                       // 2.6s
    "c_switch.md",                                                             // 0.5s
    "call_frames_pointer_after_named_unfolds.md",                              // 1.0s
    "call_frees_owned_allocation_beside_borrowed_view.md",                     // 1.0s
    "call_keeps_a_field_bearing_region_beside_the_lent_one.md",                // 1.6s
    "call_keeps_an_uncached_flat_field_beside_folded_state.md",                // 0.7s
    "call_postcondition_reads_a_two_hop_cell_inside_a_folded_view.md",         // 1.0s
    "call_refuses_a_kept_range_inside_the_allocation_it_retires.md",           // 0.5s
    "call_rejects_changed_pointer_after_named_unfolds.md",                     // 0.5s
    "call_rejects_lending_the_allocation_it_transfers.md",                     // 1.6s
    "call_retires_allocation_beside_a_view_stated_separate.md",                // 1.3s
    "call_retires_allocation_beside_unrelated_owner.md",                       // 1.2s
    "call_retires_the_allocation_it_was_lent_not_the_one_it_returns.md",       // 0.9s
    "the_back_edge_splits_a_universal_at_an_incremented_index.md",             // 0.8s
    "composite_resource_owned_buffer_len_cap_data.md",                         // 2.7s
    "composite_resource_owner_buffer_hidden_separate_projection.md",           // 0.6s
    "consecutive_reallocating_calls_keep_the_returned_allocation_readable.md", // 1.9s
    "consumed_population_count_in_ensured_predicate.md",                       // 0.6s
    "contract_owns_composite_argument.md",                                     // 1.2s
    "contract_owns_through_composite_field.md",                                // 0.7s
    "copied_bytes_through_result_need_an_explicit_transport.md",               // 1.1s
    "copy_n_segment_invariant.md",                                             // 1.4s
    "cpp_a_member_reference_parameter_retains_its_member_equality_full.md",    // 0.6s
    "cpp_guard_unwind_before_second.md",                                       // 1.4s
    "cpp_one_guard_unwind.md",                                                 // 1.0s
    "cpp_single_guard_throw_step.md",                                          // 1.1s
    "cpp_two_guard_unwind.md",                                                 // 1.8s
    "cstr_at_value_parameter_is_proved_for_every_length.md",                   // 0.8s
    "cstr_at_value_parameter_sizes_a_later_segment.md",                        // 0.7s
    "cstr_at_borrows_a_char_string_from_the_library.md",                       // 1.0s
    "cstr_at_call_map_gives_the_length_of_a_string_a_call_assembles.md",       // 0.8s
    "cstr_at_owned_value_parameter_keeps_its_length.md",                       // 1.1s
    "cstr_dynamic_indexed_read.md",                                            // 0.6s
    "cstr_strlen_through_identity_casts.md",                                   // 0.5s
    "entry_alignment_premise_expands.md",                                      // 1.4s
    "execute_order_reasoning_terminates.md",                                   // 0.7s
    "expand_sequential_null_checks.md",                                        // 1.4s
    "explicit_preserve_failure_is_prompt.md",                                  // 1.5s
    "field_borrow_parent_drop.md",                                             // 0.7s
    "field_borrow_parent_drop_rejects_stale_value.md",                         // 0.7s
    "field_derived_precise_effect_after_metadata_write.md",                    // 4.4s
    "fill_tail_rejects_tail_segment_unchanged.md",                             // 1.2s
    "forall_array_segment_rejects_overwritten_cell.md",                        // 0.5s
    "fork_join_worker_direct_contract.md",                                     // 4.9s
    "global_array_resource_element_types.md",                                  // 0.5s
    "guarded_quantified_postcondition_after_loop_expands.md",                  // 0.6s
    "have_body_solve_using_names_an_arm_binding.md",                           // 0.6s
    "heap_free_matching_allocation_authority.md",                              // 0.7s
    "holder_drop_exchanges_two_separately_held_references.md",                 // 1.2s
    "initialized_aggregate_static_arrays.md",                                  // 0.8s
    "initialized_aggregate_static_objects.md",                                 // 0.7s
    "integer_sum_range_fold.md",                                               // 0.7s
    "interior_pointer_pieces_rejoin_after_an_external_call.md",                // 0.7s
    "iterated_ownership_allocate_one.md",                                      // 0.6s
    "iterated_ownership_claim_loop.md",                                        // 1.1s
    "iterated_ownership_fold_fresh_heap_map.md",                               // 0.7s
    "iterated_ownership_whole_clause.md",                                      // 1.4s
    "iterated_ownership_release_loop.md",                                      // 1.4s
    "iterated_ownership_released_cells_feed_an_external_claim.md",             // 1.4s
    "iterated_ownership_run_scan_crosses_its_locals_ending.md",                // 1.1s
    "joined_pointer_field_read_rewrites_model_alias.md",                       // 0.7s
    "joined_pointer_field_store_rejects_overwritten_value.md",                 // 0.6s
    "joined_pointer_field_store_rewrites_model_alias.md",                      // 0.9s
    "load_variable_naming_epoch.md",                                           // 0.7s
    "loop_ascending_produces_wrong_arguments.md",                              // 0.9s
    "loop_ascending_walk_to_root.md",                                          // 1.1s
    "loop_break_exit_refold_join.md",                                          // 0.6s
    "loop_disjunctive_guard_entry_join.md",                                    // 0.5s
    "loop_entry_keeps_unfolded_state_fields_beside_its_owned_map.md",          // 0.6s
    "loop_entry_memory_capture_byte_sum.md",                                   // 1.1s
    "loop_frame_keeps_a_two_hop_map_beside_a_written_array.md",                // 1.6s
    "loop_frame_keeps_two_header_cells_of_a_field_map.md",                     // 0.8s
    "loop_frame_rejects_rewritten_base_field.md",                              // 1.9s
    "loop_invariant_through_loaded_pointer_field.md",                          // 10.1s
    "loop_invariant_through_padded_pointer_field.md",                          // 10.1s
    "loop_phase_body_reads_arm_bindings.md",                                   // 0.8s
    "loop_quantified_viewable_invariant_bounded_by_its_views_clause.md",       // 0.5s
    "loop_quantified_viewable_invariant_one_prefix_too_wide_is_refused.md",    // 1.1s
    "loop_semantically_duplicate_invariants.md",                               // 1.2s
    "loop_symbolic_disjoint_array_store_frame.md",                             // 0.6s
    "loop_three_invariant_initialization.md",                                  // 1.0s
    "memcpy_then_terminator_keeps_copied_bytes.md",                            // 0.6s
    "memcpy_then_terminator_keeps_copied_unsigned_bytes.md",                   // 1.3s
    "modular_buffer_ranges_rejoin_after_field_preserving_calls.md",            // 6.2s
    "mutex_population_missing_value_relation.md",                              // 0.6s
    "mutex_population_separate_body.md",                                       // 0.6s
    "named_root_call_preserves_aliased_pointer_field.md",                      // 6.8s
    "named_root_call_preserves_wide_field_read_congruence.md",                 // 1.2s
    "nested_loop_cursor_view_authority.md",                                    // 0.8s
    "recorded_pointer_rejects_changed_link.md",                                // 0.6s
    "opaque_call_scoped_composite_reallocation.md",                            // 1.9s
    "opaque_reallocating_call_does_not_carry_an_unstated_value.md",            // 0.8s
    "pointer_field_frame_after_descriptor_and_backing_writes.md",              // 2.9s
    "pointer_field_reloaded_backing_writes.md",                                // 0.8s
    "pointer_read_alias_after_loop_helper.md",                                 // 1.0s
    "pointer_read_alias_rejects_changed_field.md",                             // 0.6s
    "pointer_store_equation_follows_loaded_alias.md",                          // 0.5s
    "pointer_store_through_loaded_alias.md",                                   // 0.5s
    "population_conservation_local_mutex.md",                                  // 0.7s
    "population_consumption_at_close.md",                                      // 1.5s
    "population_initialized_cleanup.md",                                       // 0.8s
    "proof_branch_composite_old_memory_interface.md",                          // 0.6s
    "pure_click_functions.md",                                                 // 1.0s
    "qualified_static_resource.md",                                            // 0.5s
    "quantified_frame_rejects_a_recursive_call_on_the_array.md",               // 0.6s
    "rb_ascending_walk_to_root.md",                                            // 2.4s
    "rb_ascent_parent_link_guard.md",                                          // 1.1s
    "rb_augment_callbacks_const_suite.md",                                     // 1.5s
    "rb_augment_callbacks_helper.md",                                          // 0.8s
    "rb_augment_callbacks_helper_consumes_suite.md",                           // 0.8s
    "rb_augment_callbacks_helper_mutates_body.md",                             // 0.9s
    "rb_augment_callbacks_helper_mutates_body_stepwise.md",                    // 0.9s
    "rb_augment_callbacks_helper_owns.md",                                     // 1.0s
    "rb_augment_callbacks_helper_owns_cell_separate.md",                       // 1.0s
    "rb_augment_callbacks_helper_owns_without_separate.md",                    // 1.0s
    "rb_augment_callbacks_helper_rejects_changed_cell.md",                     // 0.8s
    "rb_augment_callbacks_rejects_mismatch.md",                                // 1.4s
    "rb_child_load_identity_rejects_a_wrong_color.md",                         // 1.0s
    "rb_first_last.md",                                                        // 8.0s
    "rb_first_rejects_wrong_frame_parent.md",                                  // 1.4s
    "rb_next.md",                                                              // 15.9s
    "rb_next_rejects_a_dropped_context.md",                                    // 16.2s
    "rb_parent_family.md",                                                     // 1.0s
    "rb_prev.md",                                                              // 15.5s
    "rb_prev_rejects_a_dropped_context.md",                                    // 16.5s
    "rb_produces_through_the_root_cell.md",                                    // 0.6s
    "rb_pure_null_pointer_argument.md",                                        // 0.5s
    "rb_refutes_the_unfolded_frame.md",                                        // 0.6s
    "rb_replace_node.md",                                                      // 4.0s
    "rb_replace_node_keeps_parent_link.md",                                    // 0.9s
    "rb_replace_node_with_children.md",                                        // 2.5s
    "reallocation_frees_old_cells_beside_their_owner.md",                      // 1.4s
    "repeated_child_retains_grown_count_requirement.md",                       // 0.9s
    "repeated_child_retains_keep_the_entry_count_bound.md",                    // 0.8s
    "resource_arm_binding_struct_base.md",                                     // 0.9s
    "resource_field_memory_endpoint.md",                                       // 0.5s
    "resource_fold_copied_packed_word.md",                                     // 0.6s
    "resource_refuted_arm_model_fact.md",                                      // 0.8s
    "resource_tree_node_init.md",                                              // 0.6s
    "resource_unfold_binds_scalar_field.md",                                   // 0.6s
    "resource_unfold_names_unmatched_body_cells.md",                           // 0.8s
    "result_parameter_false_array_postcondition.md",                           // 0.6s
    "return_fold_retains_readable_ranges_after_store.md",                      // 8.0s
    "return_fold_retains_transported_facts.md",                                // 30.6s
    "return_unfold_call_instance_with_local.md",                               // 0.6s
    "rotation_model_preserved.md",                                             // 1.0s
    "rotation_model_rejects_swapped_order.md",                                 // 0.7s
    "search_terminates_by_unmarked_count.md",                                  // 1.2s
    "separation_elements_index_word_from_an_integer_fact.md",                  // 0.6s
    "shared_child_three_parent_links_and_spare_reference.md",                  // 0.7s
    "shared_heap_detach_leak_diagnostic.md",                                   // 0.5s
    "shared_heap_detach_old_resource_handoff.md",                              // 0.8s
    "shared_heap_one_heap_parent_missing_child_ref.md",                        // 2.0s
    "shared_heap_population_certification.md",                                 // 3.8s
    "shared_heap_population_lifecycles.md",                                    // 7.2s
    "shared_heap_read_after_final_release_rejected.md",                        // 0.6s
    "shared_heap_two_parent_branch_release.md",                                // 3.8s
    "shared_heap_two_parent_caller.md",                                        // 4.0s
    "sort3_sorted.md",                                                         // 1.2s
    "static_array_parity_aggregate.md",                                        // 0.7s
    "static_array_parity_fixed_multidimensional.md",                           // 0.9s
    "static_array_parity_multidimensional.md",                                 // 0.9s
    "static_array_parity_scalar.md",                                           // 0.8s
    "static_local_arrays.md",                                                  // 0.8s
    "stdlib_every_symbol.md",                                                  // 0.9s
    "stdlib_permutation_count_over_bytes_rejects_overwrite.md",                // 0.9s
    "store_does_not_preserve_a_fold_over_the_range.md",                        // 0.5s
    "store_through_a_derived_pointer_cancels_the_base.md",                     // 2.8s
    "stored_pointer_identity_rejects_overwrite_after_call.md",                 // 1.0s
    "stored_pointer_identity_survives_resource_call.md",                       // 1.1s
    "struct_aggregate_resources.md",                                           // 1.9s
    "struct_conditional_value.md",                                             // 0.8s
    "struct_wide_integer_arrays.md",                                           // 0.6s
    "three_consecutive_reallocating_calls_keep_the_returned_allocation_readable.md", // 2.8s
    "transport_carries_a_kept_slot_cell_across_a_call.md",                     // 1.2s
    "two_opaque_reallocating_calls_do_not_carry_an_unstated_value.md",         // 0.6s
    "uint64_read_survives_store_and_resource_call.md",                         // 0.5s
    "unfold_region_then_write_a_descriptor_of_its_type.md",                    // 0.9s
    "wide_read_model_alias_in_separate_match_arms.md",                         // 0.8s
    "wide_read_model_arm_rejects_changed_word.md",                             // 0.7s
    // Measured in one four-core parallel gate run (2026-11-25).
    "a_128_bit_order_closes_through_its_integer_reading.md", // 0.8s
    "a_128_bit_order_does_not_give_a_strict_order.md",       // 0.5s
    "a_16_bit_cell_read_at_the_other_signedness_is_its_sign_cast.md", // 0.7s
    "a_32_bit_allocation_spelling_of_a_64_bit_block_is_refused.md", // 0.6s
    "a_64_bit_countdown_closes_its_back_edge.md",            // 1.7s
    "a_bounded_converted_unsigned_index_sum_is_not_split.md", // 1.0s
    "a_bounded_symbolic_read_of_a_longer_const_global_table_has_one_of_its_values.md", // 1.0s
    "a_bounded_wrapped_product_does_not_define_the_signed_one.md", // 1.9s
    "a_break_exit_counts_the_passes_before_it.md",           // 2.2s
    "a_byte_field_of_a_struct_array_element_in_a_loop_is_bounded_by_its_index.md", // 1.1s
    "a_c_local_named_iterations_is_written_program_iterations.md", // 2.4s
    "a_c_name_spelled_true_keeps_its_c_meaning.md",          // 0.6s
    "a_call_result_in_a_loop_is_spelled_by_its_loop_path.md", // 1.2s
    "a_callee_owns_a_window_of_a_64_bit_range.md",           // 1.6s
    "a_callee_reads_inside_a_chunk_a_loop_holds.md",         // 0.9s
    "a_callee_reads_past_a_chunk_a_loop_holds.md",           // 0.5s
    "a_cast_contract_a_loop_preserves_an_explicit_relationship.md", // 1.7s
    "a_closer_before_function_exit_names_itself.md",         // 0.5s
    "a_const_pointer_in_a_slice_is_the_same_value_as_a_plain_one.md", // 0.6s
    "a_constant_range_bound_is_not_named_by_a_local_holding_it.md", // 1.0s
    "a_consumed_member_bound_on_an_entry_count_is_cited.md", // 5.7s
    "a_continue_is_a_pass_of_the_loop.md",                   // 5.5s
    "a_conversion_in_range_is_its_operand_in_a_signed_certificate.md", // 0.9s
    "a_conversion_one_past_its_range_is_not_its_operand.md", // 0.7s
    "a_converted_unsigned_index_sum_is_not_split.md",        // 0.9s
    "a_definedness_requirement_at_a_composite_argument_is_met_by_conjuncts.md", // 3.1s
    "a_false_bounded_universal_over_uint64_is_refused.md",   // 0.5s
    "a_false_claim_about_a_loop_pass_count_is_refused.md",   // 7.9s
    "a_false_quantified_frame_over_a_million_elements_is_refused_promptly.md", // 0.5s
    "a_field_written_through_its_own_alias_is_not_framed.md", // 0.7s
    "a_fill_loop_claiming_one_more_byte_is_refused.md",      // 2.1s
    "a_fill_loop_over_a_size_t_range_needs_no_bound.md",     // 1.5s
    "a_free_before_a_return_inside_a_summarized_loop_body_owes_the_resource.md", // 2.3s
    "a_frozen_pointer_relationship_preserves_a_recursive_call_result.md", // 0.7s
    "a_function_level_call_is_named_among_the_function_s_calls.md", // 2.3s
    "a_global_struct_field_store_names_the_field.md",        // 1.2s
    "a_guarded_memset_postcondition_does_not_cross_a_store_of_unknown_separation.md", // 1.1s
    "a_heap_load_after_a_store_that_may_write_its_cell_splits.md", // 3.3s
    "a_heap_read_back_claimed_without_its_alias_case_is_refused.md", // 0.5s
    "a_heap_struct_array_element_field_store_in_a_loop_is_bounded_by_its_ownership.md", // 1.1s
    "a_local_struct_field_store_names_the_field.md",         // 1.1s
    "a_long_global_array_frames_the_elements_a_store_misses.md", // 1.9s
    "a_long_loop_is_ranked_by_an_int64_measure.md",          // 5.6s
    "a_long_recursion_over_constants_is_evaluated_one_level_at_a_time.md", // 2.4s
    "a_loop_body_cites_the_iteration_entry_value_a_refusal_named.md", // 1.6s
    "a_loop_call_writing_a_local_struct_forgets_its_earlier_value.md", // 2.0s
    "a_loop_call_writing_a_local_struct_keeps_the_value_its_invariant_states.md", // 2.4s
    "a_loop_condition_s_call_and_test_are_the_loop_s_own.md", // 3.9s
    "a_loop_condition_s_call_and_test_refuse_a_false_count.md", // 4.1s
    "a_loop_does_not_initialize_an_array_beside_an_initialized_one.md", // 1.3s
    "a_loop_does_not_initialize_an_element_it_never_writes.md", // 1.1s
    "a_loop_invariant_supplies_its_typed_call_domains_at_the_head.md", // 0.7s
    "a_loop_is_ranked_by_its_pass_count.md",                 // 11s
    "a_loop_keeps_a_local_array_initialized.md",             // 1.0s
    "a_loop_keeps_a_union_view_outside_its_write_set.md",    // 1.4s
    "a_loop_keeps_an_initialized_automatic_array_initialized.md", // 2.1s
    "a_loop_label_names_one_loop.md",                        // 1.2s
    "a_loop_over_a_constant_range_does_not_keep_its_entry_values.md", // 1.8s
    "a_loop_over_a_long_global_array_does_not_keep_its_entry_values.md", // 1.8s
    "a_loop_owning_a_size_t_struct_range_writes_its_fields.md", // 0.8s
    "a_loop_pass_count_names_the_passes_after_the_loop.md",  // 9.4s
    "a_loop_reading_a_constant_view_of_a_million_elements_verifies_promptly.md", // 3.8s
    "a_loop_stores_into_a_map_reached_through_a_struct_field.md", // 2.2s
    "a_loop_that_writes_a_global_union_member_forgets_its_view.md", // 1.4s
    "a_loop_that_writes_a_union_member_forgets_its_view.md", // 1.3s
    "a_loop_that_writes_calloc_storage_forgets_its_zero_reading.md", // 1.2s
    "a_loop_that_writes_other_storage_keeps_a_calloc_zero_reading.md", // 1.4s
    "a_loop_walking_a_member_array_stays_in_it.md",          // 2.5s
    "a_loop_writes_every_element_of_a_64_bit_block.md",      // 0.6s
    "a_loop_writing_through_the_struct_forgets_the_union_view.md", // 1.4s
    "a_mark_names_a_loop_head_value_after_a_long_body.md",   // 0.7s
    "a_measure_that_counts_passes_up_is_refused.md",         // 8.7s
    "a_member_pointer_kept_across_a_loop_keeps_its_subobject.md", // 1.9s
    "a_narrow_specification_sum_wraps_at_its_type.md",       // 0.6s
    "a_nested_struct_field_of_a_struct_array_element_in_a_loop_is_bounded_by_its_index.md", // 1.1s
    "a_non_strict_index_order_does_not_keep_an_earlier_store.md", // 0.8s
    "a_parent_word_frames_across_a_child_store_in_a_loop.md", // 0.7s
    "a_partition_sweep_reaches_a_range_below_its_base.md",   // 4.5s
    "a_point_a_loop_left_on_several_paths_names_no_state.md", // 2.4s
    "a_pointer_field_fact_is_not_carried_across_a_store_to_the_field.md", // 8.5s
    "a_pointer_inside_a_viewed_range_is_not_null.md",        // 0.5s
    "a_pointer_translation_bound_may_be_an_integer_observation.md", // 1.0s
    "a_population_entry_count_is_spelled_in_a_diagnostic.md", // 13s
    "a_preserve_cases_arm_keeps_a_fact_every_arm_proves.md", // 4.4s
    "a_preserve_cases_rejoin_keeps_only_the_facts_every_arm_proved.md", // 5.1s
    "a_product_that_may_wrap_is_not_its_exact_value.md",     // 1.3s
    "a_pruned_store_beside_a_field_write_is_not_forgotten.md", // 4.4s
    "a_pruned_store_in_one_branch_arm_is_not_forgotten.md",  // 2.5s
    "a_pruned_store_is_not_forgotten.md",                    // 2.2s
    "a_pruned_store_over_a_variable_span_is_not_forgotten.md", // 2.2s
    "a_pruned_store_survives_two_later_stores.md",           // 2.0s
    "a_quantified_fact_over_a_function_result_matches_a_renamed_binder.md", // 0.5s
    "a_read_back_across_a_store_no_fact_places_stays_unknown.md", // 0.9s
    "a_realloc_grows_a_64_bit_block_and_keeps_its_prefix.md", // 0.7s
    "a_realloc_of_a_32_bit_block_to_a_size_t_size_keeps_its_prefix.md", // 0.7s
    "a_reassigned_alias_of_another_pointer_does_not_read_the_first.md", // 0.9s
    "a_recursive_byte_function_evaluates_automatically.md",  // 0.8s
    "a_recursive_decreases_sum_is_an_integer.md",            // 0.8s
    "a_refusal_names_a_fact_its_renderer_cannot_spell.md",   // 1.7s
    "a_restored_cell_does_not_rejoin_an_older_state.md",     // 1.7s
    "a_retained_child_read_frames_across_a_call_through_a_loop_alias.md", // 1.1s
    "a_retained_child_read_unfolded_at_its_older_alias_needs_no_listed_alias.md", // 1.1s
    "a_retained_pointer_field_fact_needs_its_listed_loop_alias.md", // 1.3s
    "a_retained_pointer_field_fact_transports_through_a_loop_alias.md", // 1.3s
    "a_retained_word_frames_across_a_call_through_a_loop_alias.md", // 1.2s
    "a_return_inside_a_summarized_loop_body_is_a_function_exit.md", // 2.1s
    "a_return_inside_an_explicitly_preserved_loop_body_is_a_function_exit.md", // 2.1s
    "a_return_transport_source_matches_a_held_fact_up_to_its_binder.md", // 0.5s
    "a_script_that_stops_after_a_call_reports_the_remaining_goal.md", // 0.6s
    "a_script_that_stops_after_explicit_steps_executes_the_rest.md", // 0.6s
    "a_script_that_stops_with_c_left_is_finished.md",        // 0.6s
    "a_second_universal_have_narrows_a_stated_range.md",     // 2.2s
    "a_self_aliased_field_operand_is_one_value.md",          // 0.6s
    "a_self_aliased_field_sum_without_bounds_is_refused.md", // 1.0s
    "a_sign_cast_of_a_nonnegative_quotient_is_the_quotient_at_the_other_signedness.md", // 0.8s
    "a_signed_byte_keeps_its_negative_value_through_storage_and_calls.md", // 0.6s
    "a_size_t_loop_stepping_by_two_closes_with_arithmetic.md", // 3.0s
    "a_size_t_loop_stepping_by_two_closes_with_explicit_steps.md", // 3.4s
    "a_size_t_struct_array_calloc_block_writes_and_reads_its_fields.md", // 0.7s
    "a_size_t_struct_array_malloc_block_writes_and_reads_its_fields.md", // 0.7s
    "a_slice_call_in_a_click_theorem_expands_in_click_spellings.md", // 2.0s
    "a_stated_store_search_fact_keeps_the_heap_cell.md",     // 1.1s
    "a_static_array_read_is_spelled_by_its_element.md",      // 13s
    "a_store_at_another_symbolic_element_keeps_a_cached_one.md", // 3.1s
    "a_store_at_the_last_heap_element_keeps_the_first.md",   // 0.9s
    "a_store_at_the_last_size_t_heap_element_keeps_the_first.md", // 0.7s
    "a_store_index_bound_and_disequality_keep_a_cached_element.md", // 1.0s
    "a_store_index_fact_may_be_stated_as_the_integer_or_the_word.md", // 2.0s
    "a_store_index_fact_may_be_the_integer_or_the_word.md",  // 1.1s
    "a_store_kept_by_a_distinctness_fact_still_stops_a_read.md", // 1.7s
    "a_store_to_a_retained_child_read_is_not_framed.md",     // 2.1s
    "a_store_to_the_parent_word_is_not_framed.md",           // 0.6s
    "a_stored_break_test_closes_the_back_edge.md",           // 2.3s
    "a_string_literal_provides_its_c_string_view.md",        // 2.5s
    "a_struct_array_element_field_load_in_a_loop_is_bounded_by_its_index.md", // 1.1s
    "a_struct_array_element_second_field_store_past_the_last_element_is_refused.md", // 0.7s
    "a_struct_equality_compares_every_field.md",             // 0.5s
    "a_struct_equality_is_not_its_first_field.md",           // 0.8s
    "a_summarized_loop_body_return_is_certified_with_its_value.md", // 2.0s
    "a_uint64_sum_that_may_wrap_is_not_arithmetic.md",       // 0.9s
    "a_uint8_loop_counter_ranks_as_a_promoted_int32.md",     // 1.8s
    "a_viewable_premise_from_an_earlier_point_prints_that_point.md", // 0.9s
    "a_window_two_offsets_past_the_end_is_refused.md",       // 4.8s
    "a_word_the_call_may_write_is_not_framed_across_it.md",  // 2.2s
    "a_written_branch_interface_carries_what_an_invariant_needs.md", // 1.9s
    "a_written_viewable_range_span_does_not_prove_a_tighter_bound.md", // 2.5s
    "a_wrong_pass_count_after_the_loop_is_refused.md",       // 9.8s
    "a_wrong_snprintf_count_is_refused.md",                  // 1.1s
    "abstract_resource_field_call_facts_support_arithmetic.md", // 1.0s
    "abstract_resource_field_precondition_after_call.md",    // 1.8s
    "aggregate_parameter_symbolic_index.md",                 // 0.5s
    "algebraic_structural_induction_rejects_unmet_requirement.md", // 1.2s
    "aliased_caller_field_rejects_overwrite.md",             // 7.5s
    "aliased_caller_field_survives_call.md",                 // 0.5s
    "an_aggregate_copy_carries_a_forgotten_initialized_field.md", // 1.5s
    "an_aggregate_copy_from_a_never_written_member_stays_undefined.md", // 1.2s
    "an_array_inside_a_struct_array_element_in_a_loop_is_bounded_by_both_indices.md", // 1.2s
    "an_automatically_closed_loop_closes_each_branch_arm.md", // 3.2s
    "an_automatically_closed_loop_splits_at_its_c_branches.md", // 6.7s
    "an_entry_view_names_the_entry_address.md",              // 1.0s
    "an_equal_loaded_pointer_does_not_justify_a_false_field_fact.md", // 0.9s
    "an_if_form_fact_survives_a_disjoint_store.md",          // 0.8s
    "an_if_interface_exports_a_quantified_fact_with_an_integer_bound.md", // 1.1s
    "an_index_ordered_through_an_equal_index_keeps_an_earlier_store.md", // 1.6s
    "an_induction_hypothesis_applies_in_a_have_and_a_match_nested_either_way.md", // 1.8s
    "an_induction_hypothesis_applies_inside_a_have.md",      // 1.9s
    "an_induction_hypothesis_applies_inside_match_arms.md",  // 0.9s
    "an_induction_premise_is_named_when_it_is_not_available.md", // 0.9s
    "an_infeasible_path_with_a_closed_order_goal_closes.md", // 0.6s
    "an_initializer_produces_the_memory_it_initialized.md",  // 0.8s
    "an_inner_loop_counts_its_own_passes.md",                // 5.3s
    "an_int_count_struct_array_malloc_block_writes_and_reads_its_fields.md", // 2.0s
    "an_integer_argument_of_a_generic_theorem_is_read_as_an_integer.md", // 1.3s
    "an_integer_stated_body_fact_assembles_a_c_string_view.md", // 1.8s
    "an_integer_stated_body_fact_needs_its_range_bound.md",  // 1.4s
    "an_interface_fact_needs_its_terms_defined_in_each_arm.md", // 3.8s
    "an_omitted_preserve_splits_a_comparison_assigned_to_a_local.md", // 6.4s
    "an_omitted_theorem_proof_is_solve.md",                  // 0.5s
    "an_ordinary_exit_produces_a_composite_whose_body_facts_hold.md", // 2.2s
    "an_unfold_through_an_alias_keeps_the_owners_cell_names.md", // 1.6s
    "an_unfolded_quantifier_does_not_capture_a_same_named_argument.md", // 0.8s
    "an_unfolded_range_all_does_not_capture_a_same_named_argument.md", // 0.9s
    "an_unsigned_loop_counter_store_is_bounded_by_a_variable_guard.md", // 0.7s
    "an_unsigned_loop_counter_store_is_bounded_by_its_guard.md", // 0.7s
    "an_unsigned_loop_to_a_variable_bound_owes_an_unsigned_descent.md", // 0.6s
    "apply_argument_names_a_parameter_the_loop_reassigns.md", // 0.7s
    "apply_closes_mirrored_order_spelling.md",               // 1.0s
    "apply_does_not_supply_a_conclusion_its_theorem_lacks.md", // 0.7s
    "apply_induction_finds_a_premise_stated_from_the_other_side.md", // 1.0s
    "apply_theorem_to_an_entry_array_refuses_a_current_premise.md", // 0.7s
    "arena_prefix_free_reads_region_arena.md",               // 1.1s
    "arithmetic_after_loop_seed_rewrite.md",                 // 0.7s
    "arithmetic_bounds_a_strict_lower_side_below_int32_max.md", // 1.9s
    "arithmetic_conjunction_extraction.md",                  // 0.8s
    "arithmetic_definedness_is_one_ordinary_domain.md",      // 0.8s
    "arithmetic_does_not_bound_a_non_strict_lower_side_below_int32_max.md", // 0.6s
    "arithmetic_domains_call_precondition.md",               // 0.6s
    "arithmetic_even_wrapping_divisor_can_be_zero.md",       // 1.1s
    "arithmetic_expression_bounded_signed_shift_can_overflow.md", // 1.6s
    "arithmetic_expression_conditional_signed_shift.md",     // 2.3s
    "arithmetic_expression_guarded_signed_product_overflow.md", // 1.7s
    "arithmetic_expression_guarded_signed_ring.md",          // 0.6s
    "arithmetic_expression_mask_add_bounds.md",              // 0.6s
    "arithmetic_expression_signed_literal_shift_reaches_sign_bit.md", // 0.6s
    "arithmetic_expression_signed_shift_unsigned_count_overflow.md", // 1.4s
    "arithmetic_keeps_an_operand_bound_beside_a_one_sided_premise.md", // 1.6s
    "arithmetic_on_an_unfold_refreshed_goal.md",             // 0.7s
    "arithmetic_one_sided_premise_still_needs_the_operand_bound.md", // 3.3s
    "arithmetic_positive_divisor_product_guards.md",         // 0.7s
    "arithmetic_positive_divisor_product_needs_lower_guard.md", // 3.7s
    "arithmetic_proves_a_disequality_by_refuting_its_equality.md", // 1.1s
    "arithmetic_safety_right_shift_count.md",                // 0.8s
    "arithmetic_shifted_one_count_bounds.md",                // 0.6s
    "arithmetic_uint32_mask_refusal_names_no_signed_overflow.md", // 0.6s
    "arithmetic_using_chains_equalities.md",                 // 0.6s
    "arithmetic_using_reads_unsigned_type_ranges.md",        // 0.6s
    "arm_contradiction_after_loop_reports_its_source.md",    // 0.7s
    "arm_identity_read_alias_write_refused_id.md",           // 0.9s
    "arm_identity_read_alias_write_refused_p.md",            // 1.0s
    "arm_identity_read_node_write_refused_p.md",             // 0.7s
    "array_fact_does_not_survive_a_branch_that_may_write_it.md", // 1.0s
    "array_fact_does_not_survive_a_call_that_may_write_it.md", // 0.7s
    "array_fact_does_not_survive_a_call_that_writes_a_sibling_array.md", // 0.8s
    "array_fact_does_not_survive_a_callee_that_frees_the_array.md", // 1.2s
    "array_fact_does_not_survive_a_recursive_call_on_the_array.md", // 1.8s
    "array_fact_does_not_survive_a_store_into_a_global.md",  // 1.2s
    "array_fact_does_not_survive_a_store_into_a_sibling_array.md", // 1.4s
    "array_fact_does_not_survive_freeing_the_array.md",      // 1.3s
    "authority_count_defined_at_max_rejected.md",            // 1.5s
    "authority_exact_symbolic_batch_overconsume.md",         // 1.3s
    "authority_exact_symbolic_batch_partial_spend.md",       // 1.3s
    "authority_exact_symbolic_population_total_wrong.md",    // 1.4s
    "authority_family_exchange.md",                          // 0.8s
    "authority_family_exchange_missing_capacity_authority.md", // 0.7s
    "authority_family_exchange_missing_object.md",           // 0.6s
    "authority_family_exchange_stack_object.md",             // 0.8s
    "authority_family_exchange_stack_payload_unavailable.md", // 1.8s
    "authority_loop_contract_certifies.md",                  // 1.1s
    "authority_mixed_birth_arbitrary_entry.md",              // 1.4s
    "authority_mixed_birth_keeps_numeric_delta.md",          // 2.7s
    "authority_mutex_locked_exchange_unspent_rejected.md",   // 1.8s
    "authority_mutex_locked_release_stale_rejected.md",      // 0.6s
    "authority_mutex_locked_retain_without_cap_rejected.md", // 0.5s
    "authority_mutex_locked_workers_call_before_join.md",    // 0.5s
    "authority_named_import_cross_pool_transfer.md",         // 0.6s
    "authority_named_import_wildcard_creation.md",           // 0.6s
    "authority_numeric_population_total.md",                 // 0.9s
    "authority_numeric_population_total_maximum.md",         // 0.9s
    "authority_observe_symbolic_count_is_not_a_total.md",    // 0.6s
    "authority_owned_count_after_consume.md",                // 0.6s
    "authority_pool_checkout_without_slot_rejected.md",      // 0.5s
    "authority_pool_control_missing_consumption.md",         // 0.9s
    "authority_pool_control_missing_production.md",          // 4.7s
    "authority_pool_control_wrong_counter.md",               // 1.4s
    "authority_symbolic_batch_retirement.md",                // 1.2s
    "authority_symbolic_batch_retirement_partial.md",        // 1.1s
    "authority_symbolic_batch_retirement_wrong_total.md",    // 3.7s
    "authority_symbolic_birth_composition.md",               // 0.9s
    "authority_symbolic_birth_composition_missing_bound.md", // 0.7s
    "authority_symbolic_birth_composition_wrong_total.md",   // 1.4s
    "authority_two_to_one_quantity_missing_input.md",        // 0.8s
    "authority_two_to_one_quantity_reuse_rejected.md",       // 0.8s
    "authority_wildcard_consume_private_body.md",            // 0.6s
    "authority_wildcard_consume_private_body_use_after_free.md", // 1.0s
    "authority_wildcard_create_private_body_nested.md",      // 0.6s
    "authority_wildcard_exact_count.md",                     // 0.6s
    "authority_wildcard_transfer_private_body_aliased_pools.md", // 0.6s
    "authority_wildcard_transfer_private_body_reuse_source.md", // 0.7s
    "authority_wildcard_transfer_private_body_wrong_total.md", // 0.5s
    "back_edge_closes_an_unsigned_bound_from_the_guard.md",  // 0.6s
    "bare_transport_names_its_uncarried_leaf.md",            // 0.6s
    "borrowed_window_returns_what_was_lent.md",              // 0.7s
    "bounded_byte_increment.md",                             // 1.1s
    "byte_pointer_association.md",                           // 0.5s
    "byte_pointer_association_requires_selected_definedness.md", // 0.8s
    "byte_range_theorem_application_owes_its_span_half.md",  // 0.7s
    "byte_representation_buffer_byte_read.md",               // 0.6s
    "byte_view_read_through_char_pointer_prints_its_type.md", // 1.2s
    "c_array_compound_literal_while_condition.md",           // 1.3s
    "c_call_binder_transport_tighter_bound.md",              // 0.5s
    "c_callback_bare_designator.md",                         // 0.6s
    "c_contract_executes_mutation.md",                       // 0.7s
    "c_decreases_count_up.md",                               // 2.1s
    "c_decreases_integer_measure_recursion.md",              // 0.8s
    "c_decreases_lexicographic_loop.md",                     // 2.4s
    "c_decreases_lexicographic_recursion.md",                // 2.2s
    "c_decreases_lexicographic_recursion_rejects_negative_component.md", // 1.0s
    "c_decreases_lexicographic_recursion_rejects_swapped_order.md", // 1.8s
    "c_decreases_lexicographic_recursion_under_loops.md",    // 5.2s
    "c_decreases_lexicographic_recursion_under_loops_must_descend.md", // 4.2s
    "c_decreases_loop.md",                                   // 1.2s
    "c_decreases_loop_inline_helper.md",                     // 1.4s
    "c_decreases_memory_measure_recursion.md",               // 2.4s
    "c_decreases_model_measure_mutual_recursion.md",         // 0.9s
    "c_decreases_model_measure_mutual_recursion_must_descend.md", // 1.3s
    "c_decreases_model_measure_recursion_consumes_inside_loop.md", // 1.3s
    "c_decreases_nested_loop.md",                            // 4.8s
    "c_decreases_parameter_avoids_recursive_loop.md",        // 0.7s
    "c_decreases_parameter_reassignment_descends.md",        // 0.5s
    "c_decreases_proof_branch_shared_loop.md",               // 2.5s
    "c_decreases_proof_branch_shared_loop_rejects_constant.md", // 2.2s
    "c_decreases_proof_branches_own_distinct_measures.md",   // 5.7s
    "c_decreases_pure_expression_mutual_recursion.md",       // 4.2s
    "c_decreases_pure_expression_mutual_recursion_must_descend.md", // 4.0s
    "c_decreases_pure_expression_mutual_recursion_rejects_mixed_shapes.md", // 2.2s
    "c_decreases_pure_expression_mutual_recursion_requires_every_measure.md", // 2.0s
    "c_decreases_pure_expression_recursion.md",              // 2.0s
    "c_decreases_pure_expression_recursion_in_havocked_loop.md", // 3.3s
    "c_decreases_pure_expression_recursion_in_loop.md",      // 2.7s
    "c_decreases_recursive_in_loop.md",                      // 1.6s
    "c_decreases_rejects_bad_loop_path.md",                  // 1.0s
    "c_decreases_rejects_inline_helper_loop.md",             // 0.7s
    "c_decreases_rejects_negative_ranking_component.md",     // 0.8s
    "c_decreases_rejects_non_decreasing_lexicographic_loop.md", // 0.9s
    "c_decreases_rejects_recursive_inline_helper.md",        // 0.7s
    "c_finite_forall_rejects_wider_second_guard.md",         // 1.1s
    "c_for_loop.md",                                         // 1.8s
    "c_guarded_resource_disjoint_store_changed.md",          // 0.5s
    "c_memory_lvalue_updates.md",                            // 0.6s
    "c_named_contract_refinement_unfolds_old_current_predicate.md", // 0.6s
    "c_named_function_contract_accepts_smaller_mutable_footprint.md", // 0.7s
    "c_named_function_contract_accepts_symbolic_borrowed_subrange.md", // 0.7s
    "c_named_function_contract_frames_concrete_owned_subrange.md", // 0.7s
    "c_named_function_contract_mismatch.md",                 // 6.6s
    "c_named_function_contract_refinement.md",               // 0.8s
    "c_named_function_contract_refinement_resources.md",     // 0.7s
    "c_named_function_contract_refines_disjunctive_clause.md", // 0.8s
    "c_named_function_contract_refines_rewritten_decrease_guarantee.md", // 0.7s
    "c_named_function_contract_refines_stateful_postcondition.md", // 0.7s
    "c_named_function_contract_refines_vacuous_guarded_clause.md", // 0.8s
    "c_named_function_contract_rejects_weaker_postcondition.md", // 0.7s
    "c_owned_pointer_resource_modular_loop.md",              // 1.5s
    "c_pointer_field_copy_preserves_borrowed_view_across_call.md", // 0.9s
    "c_pointer_field_prefix_postcondition_across_call.md",   // 3.8s
    "c_pointer_field_subrange_write_preserves_resources.md", // 4.8s
    "c_pointer_local_loop_invariant.md",                     // 2.1s
    "c_reads_through_a_resource_with_fields_across_a_loop.md", // 2.0s
    "c_reads_through_an_owned_resource_inside_a_loop.md",    // 1.4s
    "c_static_function.md",                                  // 4.1s
    "c_static_function_body_is_checked.md",                  // 0.6s
    "c_struct_compound_literal_argument.md",                 // 0.6s
    "c_struct_compound_literal_loop.md",                     // 1.2s
    "c_struct_compound_literal_loop_unbraced.md",            // 1.2s
    "c_struct_compound_literal_while_condition.md",          // 1.3s
    "call_checked_input_facts_keep_prestate.md",             // 1.8s
    "call_havoc_symbolic_write_set.md",                      // 0.6s
    "call_inside_open_population_does_not_assume_its_body.md", // 0.5s
    "call_step_refuses_contradictory_old_array_bound.md",    // 2.9s
    "call_step_retains_old_array_bound.md",                  // 2.9s
    "call_through_deep_instance_chain_footprint_includes_its_memory.md", // 0.6s
    "call_through_instance_footprint_includes_its_memory.md", // 0.8s
    "call_through_matched_arm_child_footprint_includes_its_memory.md", // 0.6s
    "call_through_witness_footprint_includes_its_memory.md", // 4.0s
    "calls_in_short_circuit_operands.md",                    // 0.7s
    "cases_at_a_frontier_finishes_each_arm.md",              // 0.7s
    "cases_in_a_loop_body_rejoins.md",                       // 1.5s
    "char_argument_to_byte_predicate_unfolds_as_bytes.md",   // 0.9s
    "checked_call_termination_loop_summary.md",              // 0.8s
    "child_release_branch_on_count.md",                      // 1.7s
    "compound_definedness_theorem_premise_missing_outer.md", // 0.6s
    "conditional_call_indexed_result_fact.md",               // 0.7s
    "consumed_population_predicate_rejects_missing_consumption.md", // 0.5s
    "contract_clause_forms.md",                              // 0.6s
    "copy3_array_demo.md",                                   // 3.5s
    "count_to_loop_initialize_by_solve_and_preserve.md",     // 1.8s
    "count_to_n_loop_invariant.md",                          // 1.8s
    "count_to_three_loop_invariants.md",                     // 1.2s
    "counted_resource_refcount_transitions.md",              // 1.0s
    "cpp_class_const_method_keeps_fields.md",                // 1.1s
    "cpp_class_const_method_keeps_fields_rejects_overclaim.md", // 1.2s
    "cpp_class_const_reference_keeps_fields.md",             // 1.8s
    "cpp_class_const_reference_lends_the_object.md",         // 0.6s
    "cpp_class_object_state.md",                             // 1.0s
    "cpp_class_object_state_mutable.md",                     // 2.0s
    "cpp_class_object_state_mutable_override_establishes_the_interface.md", // 1.0s
    "cpp_class_object_state_mutable_reference_returns_new_state.md", // 1.3s
    "cpp_class_object_state_mutable_this_calls.md",          // 2.5s
    "cpp_class_object_state_override_keeps_the_interface.md", // 1.1s
    "cpp_class_resource_state_lent_as_const.md",             // 0.8s
    "cpp_class_resource_state_lent_as_const_rejects_overclaim.md", // 0.9s
    "cpp_class_resource_state_override_calls_a_helper.md",   // 1.0s
    "cpp_class_subclass_inherits_a_method_it_keeps.md",      // 1.4s
    "cpp_class_subclass_local_object_packs_itself.md",       // 2.0s
    "cpp_class_subclass_override_keeps_the_interface.md",    // 1.4s
    "cpp_class_subclass_override_rejects_overclaim.md",      // 1.1s
    "cpp_class_template_const_overloads.md",                 // 1.4s
    "cpp_class_template_object_state.md",                    // 1.1s
    "cpp_class_template_override_calls_its_own_method.md",   // 0.9s
    "cpp_class_template_verified_once.md",                   // 1.5s
    "cpp_generic_class_state_ignored_is_refused.md",         // 1.2s
    "cpp_generic_class_state_in_a_resource.md",              // 8.3s
    "cpp_generic_pop_on_empty_is_refused.md",                // 1.6s
    "cpp_generic_push_cannot_keep_its_list.md",              // 1.1s
    "cpp_lambda_named_contract.md",                          // 0.8s
    "cpp_lambda_named_contract_rejects_weaker_postcondition.md", // 0.7s
    "cpp_noexcept_calls_while_a_guard_lives_execute.md",     // 0.5s
    "cpp_polymorphic_base_construction.md",                  // 1.4s
    "cpp_polymorphic_base_destructor_runs_after.md",         // 0.8s
    "cpp_polymorphic_base_destructor_runs_after_rejects_overclaim.md", // 1.0s
    "cpp_polymorphic_destructor_rejects_overclaim.md",       // 1.0s
    "cpp_polymorphic_destructor_runs_its_body.md",           // 0.6s
    "cpp_polymorphic_local_construction.md",                 // 1.2s
    "cpp_polymorphic_local_construction_rejects_overclaim.md", // 1.4s
    "cpp_polymorphic_virtual_destructor.md",                 // 1.1s
    "cpp_record_pointers.md",                                // 1.0s
    "cpp_stack_pop_cannot_keep_its_list.md",                 // 6.1s
    "cpp_virtual_call_through_a_derived_class_reference.md", // 1.8s
    "cpp_virtual_method_interface.md",                       // 2.7s
    "cpp_virtual_override_keeps_the_inherited_guarantee.md", // 2.6s
    "cpp_virtual_override_renames_its_parameters.md",        // 3.0s
    "cstr_at_fold_refuses_a_wrong_length.md",                // 0.9s
    "cstr_at_owner_open_names_the_body_fact_left_at_close.md", // 0.7s
    "cstr_at_value_parameter_refuses_a_wrong_length_claim.md", // 0.8s
    "cstr_dynamic_invalidated_transport.md",                 // 0.7s
    "definedness_before_a_rewritten_sum_claim.md",           // 1.4s
    "definedness_is_a_step_requirement.md",                  // 0.6s
    "dereferenced_reads_across_writes.md",                   // 3.2s
    "designated_scalar_static_arrays.md",                    // 1.4s
    "diverges_rejects_unjustified_marker.md",                // 0.8s
    "do_while_rejects_wrong_output_model.md",                // 0.8s
    "do_while_restored_field_frame_remains_separate.md",     // 0.6s
    "do_while_restored_frame_remains_separate.md",           // 0.6s
    "do_while_return_after_prefold_rejects_wrong_model.md",  // 0.5s
    "do_while_returns_rebound_resources.md",                 // 0.5s
    "element_offsets_from_exact_index_sum.md",               // 1.9s
    "empty_loop_footprint_preserves_nested_read_transport.md", // 4.4s
    "exact_address_owner_beside_symbolic_prefix.md",         // 0.6s
    "execute_expands_certified_post_call_fact.md",           // 0.6s
    "execute_in_a_proof_if_arm_splits_alias_cases_inside_a_c_if.md", // 0.6s
    "execute_preserves_derived_call_premise.md",             // 0.9s
    "execute_until_back_edge.md",                            // 1.8s
    "execute_until_back_edge_of_a_named_loop.md",            // 1.8s
    "execute_until_runs_to_a_statement_region.md",           // 1.0s
    "execute_until_selects_loop_entry.md",                   // 1.7s
    "explicit_guarded_postcondition_closes_after_call.md",   // 1.2s
    "explicit_integer_algebra_laws.md",                      // 0.5s
    "explicit_transport_carries_guarded_definedness.md",     // 0.5s
    "field_separation_preserves_abi_width.md",               // 0.6s
    "field_separation_rejects_overwrite.md",                 // 8.7s
    "file_scope_static_arrays.md",                           // 0.9s
    "file_scope_tentative_arrays.md",                        // 0.9s
    "file_scope_tentative_globals.md",                       // 0.8s
    "fill3_array_loop.md",                                   // 3.1s
    "fill_n_loop_mutable_segment.md",                        // 2.0s
    "fill_n_symbolic_pointer_loop.md",                       // 2.1s
    "fill_tail_keeps_first.md",                              // 2.6s
    "fill_tail_old_prefix_segment.md",                       // 2.8s
    "fold_at_arm_identity_after_store_to_other_node.md",     // 0.5s
    "fold_by_with_both_rechecks_after_execute.md",           // 2.0s
    "fold_function_is_nonnegative_by_induction.md",          // 3.9s
    "fold_index_substitution_does_not_reuse_pre_call_reads.md", // 0.6s
    "fold_join_needs_the_endpoint_equality.md",              // 0.6s
    "fold_joins_ranges_abutting_by_proved_equality.md",      // 0.5s
    "fold_pointer_argument_body_fact_rejects_other_owner.md", // 5.2s
    "fold_read_solve_extends_endpoint_with_zero_contribution.md", // 7.6s
    "fold_read_transport_across_a_call_with_a_checked_write_set.md", // 3.5s
    "fold_read_transport_below_a_nonzero_start.md",          // 1.0s
    "fold_read_transport_grants_no_c_read.md",               // 5.5s
    "fold_read_transport_historical_endpoint.md",            // 1.2s
    "fold_read_transport_reads_in_both_arms.md",             // 5.4s
    "fold_read_transport_rejects_a_call_writing_the_range.md", // 3.2s
    "fold_read_transport_rejects_a_changed_base_pointer.md", // 6.7s
    "fold_read_transport_rejects_a_changed_endpoint.md",     // 1.0s
    "fold_read_transport_rejects_a_global_that_may_be_the_array.md", // 3.0s
    "fold_read_transport_rejects_a_missing_index_bound.md",  // 2.3s
    "fold_read_transport_rejects_a_read_outside_the_range.md", // 0.8s
    "fold_read_transport_rejects_an_opaque_helper.md",       // 5.5s
    "fold_read_transport_rejects_an_unseparated_alias.md",   // 8.5s
    "fold_read_transport_through_a_separated_alias.md",      // 0.7s
    "fold_reading_a_viewed_array_is_nonnegative_over_its_own_range.md", // 2.2s
    "fold_reading_an_array_is_nonnegative_by_induction.md",  // 6.9s
    "fold_reading_an_array_is_nonnegative_over_its_own_range.md", // 2.2s
    "forall_viewable_range.md",                              // 2.0s
    "forward_goto_from_summarized_loop.md",                  // 0.8s
    "fprintf_ignores_arguments_its_format_does_not_convert.md", // 2.4s
    "fprintf_refuses_a_format_that_converts.md",             // 1.0s
    "freeing_call_keeps_a_caller_owned_descriptor_beside_the_array.md", // 0.6s
    "frontier_have_execute_until_and_mark.md",               // 2.2s
    "full_width_pointer_association.md",                     // 0.5s
    "full_width_pointer_cursor_loop.md",                     // 3.9s
    "global_union_members_sharing_bytes_keep_the_offset.md", // 1.4s
    "goto_out_may_skip_loops_that_precede_its_label.md",     // 1.3s
    "grouped_proof_covers_claims_without_their_own.md",      // 3.5s
    "guarded_definedness_does_not_hide_an_overlapping_store.md", // 0.9s
    "guarded_definedness_does_not_survive_free.md",          // 0.7s
    "guarded_definedness_survives_a_disjoint_store.md",      // 0.5s
    "guarded_postcondition_unbounded_stays_guarded.md",      // 0.5s
    "guarded_resource_read_rejects_changed_field.md",        // 0.5s
    "have_by_solve_chains_a_scaled_bound.md",                // 0.7s
    "have_by_solve_refutes_a_linear_bound.md",               // 0.7s
    "have_disjunction_projection_missing_arm.md",            // 0.6s
    "have_viewable_outside_the_range_rejected.md",           // 0.5s
    "have_viewable_prefix_of_a_range.md",                    // 1.8s
    "have_viewable_single_cell.md",                          // 4.2s
    "implicit_grouped_proof_reports_the_failing_claim.md",   // 1.0s
    "indexed_expressions_survive_separated_stores.md",       // 6.3s
    "indexed_fold_preserves_descriptor_loop_ownership.md",   // 13s
    "indexed_reads_across_multi_write_calls.md",             // 4.1s
    "indexed_reads_across_two_stores.md",                    // 3.5s
    "indexed_reads_in_bitwise_expressions.md",               // 2.0s
    "indexed_reads_in_literal_comparisons.md",               // 6.2s
    "indexed_reads_in_wrapped_expressions.md",               // 2.9s
    "indexed_write_borrow_obligation.md",                    // 1.2s
    "induction_hypothesis_cites_a_listed_range_with_its_span.md", // 2.1s
    "induction_hypothesis_owes_the_range_span.md",           // 8.3s
    "inline_helper_contract_is_the_call_boundary.md",        // 1.0s
    "inline_helper_expression_measure_recursion.md",         // 0.8s
    "inline_helper_ranked_loop.md",                          // 0.9s
    "instantiate_a_memory_invariant_with_a_computed_bound.md", // 0.9s
    "instantiate_a_wide_memory_invariant_with_a_computed_bound.md", // 0.8s
    "int16_uint16_conversion.md",                            // 0.5s
    "int32_defined_bounds_do_not_exclude_overflow.md",       // 0.8s
    "int32_defined_from_bounds.md",                          // 2.6s
    "int32_defined_one_operand_bounded.md",                  // 0.7s
    "int32_division_excluded_by_a_disjunction_is_defined.md", // 0.8s
    "int64_defined_from_bounds.md",                          // 1.9s
    "int64_read_survives_store_and_resource_call.md",        // 0.8s
    "int8_conversion.md",                                    // 0.7s
    "integer_certificate_refutation_and_rounding.md",        // 0.7s
    "integer_correction_endpoint_bounds.md",                 // 0.5s
    "integer_operation_identity_of_a_product.md",            // 0.6s
    "integer_pointer_array_widths.md",                       // 0.5s
    "integer_quotient_strict_bound.md",                      // 1.4s
    "integer_rounded_product_bounds.md",                     // 1.8s
    "integer_uint32_checked_product_observations.md",        // 0.7s
    "invariant_population_body_requires_restore.md",         // 0.6s
    "join_rejects_changed_uncached_read.md",                 // 0.6s
    "joined_pointer_field_read_rejects_different_field.md",  // 1.3s
    "later_loop_preserve.md",                                // 1.4s
    "local_array_loop_frame.md",                             // 1.2s
    "loop_after_proof_branch_expands.md",                    // 1.8s
    "loop_ascending_frame_refold_rejected.md",               // 0.6s
    "loop_binder_counter_model.md",                          // 3.4s
    "loop_binder_counter_model_concise_proof.md",            // 2.5s
    "loop_binder_instance_footprint_includes_its_memory.md", // 7.0s
    "loop_binder_model_needs_an_invariant.md",               // 1.5s
    "loop_binder_rebinds_by_arguments.md",                   // 2.6s
    "loop_binder_rejects_false_model_invariant.md",          // 2.8s
    "loop_binder_takes_over_a_call_result.md",               // 0.8s
    "loop_binder_takes_over_unfolded_cross_family_child.md", // 0.9s
    "loop_body_break_exit.md",                               // 0.6s
    "loop_body_continue_back_edge.md",                       // 0.8s
    "loop_body_proof_match.md",                              // 2.1s
    "loop_body_proof_match_arm_drops_binder.md",             // 1.4s
    "loop_body_proof_match_concise_proof.md",                // 2.2s
    "loop_body_proof_match_ensuring_inside_a_proof_if.md",   // 6.9s
    "loop_body_proof_match_ensuring_old_fact.md",            // 2.1s
    "loop_body_proof_match_ensuring_rejoins.md",             // 2.1s
    "loop_body_proof_match_shared_continuation.md",          // 0.9s
    "loop_body_proof_match_two_live_arms.md",                // 3.7s
    "loop_body_refutes_an_unfolded_child.md",                // 1.2s
    "loop_bundle_names_a_quantified_invariant_binder_as_written.md", // 3.9s
    "loop_clause_reads_arm_bindings.md",                     // 2.2s
    "loop_conditional_views_memory.md",                      // 1.9s
    "loop_conjunctive_guard_exits.md",                       // 3.8s
    "loop_decreases_index_ordered_walk.md",                  // 0.5s
    "loop_decreases_integer_measure.md",                     // 0.9s
    "loop_decreases_integer_measure_must_decrease.md",       // 0.6s
    "loop_decreases_model_function_must_stay_nonnegative.md", // 0.8s
    "loop_decreases_pure_expression.md",                     // 2.6s
    "loop_decreases_pure_expression_must_decrease.md",       // 3.6s
    "loop_decreases_reads_a_field.md",                       // 1.5s
    "loop_decreases_reads_a_field_the_body_writes.md",       // 1.2s
    "loop_decreases_rejects_a_field_that_moves.md",          // 4.2s
    "loop_decreases_strict_descendant.md",                   // 1.3s
    "loop_decreases_uses_its_counter_bounds.md",             // 1.4s
    "loop_default_havoc_frames_viewed_only_contract.md",     // 1.9s
    "loop_default_havoc_keeps_mutable_segment.md",           // 1.4s
    "loop_entry_guard_before_written_implication.md",        // 1.4s
    "loop_entry_guard_intro.md",                             // 2.9s
    "loop_entry_memory_capture_countdown.md",                // 1.4s
    "loop_entry_memory_capture_cursor.md",                   // 8.6s
    "loop_entry_memory_capture_postdecrement.md",            // 0.7s
    "loop_entry_memory_capture_wide_countdown.md",           // 0.7s
    "loop_entry_program_point.md",                           // 1.1s
    "loop_entry_program_point_rejected.md",                  // 1.5s
    "loop_exit_diagnostic_names_live_model.md",              // 0.6s
    "loop_exit_program_point.md",                            // 1.7s
    "loop_final_iteration_free.md",                          // 0.8s
    "loop_follows_quantified_successor_bound.md",            // 2.1s
    "loop_global_not_havoced_rejected.md",                   // 2.8s
    "loop_head_write_separation.md",                         // 2.0s
    "loop_initialize_helper_have_before_the_closer.md",      // 1.7s
    "loop_initialize_narrows_a_held_byte_range_under_a_universal.md", // 2.3s
    "loop_initialize_narrows_a_held_byte_range_without_a_count_bound.md", // 2.4s
    "loop_initialize_narrows_a_held_range_under_a_universal.md", // 4.0s
    "loop_initialize_smart_have_per_invariant.md",           // 1.7s
    "loop_inside_a_branch_arm.md",                           // 1.9s
    "loop_inside_a_branch_arm_rejects_a_false_invariant.md", // 2.4s
    "loop_inside_a_branch_else_arm.md",                      // 1.2s
    "loop_inside_a_proof_if_arm.md",                         // 1.9s
    "loop_invariant_binds_model_from_a_folded_parent.md",    // 0.8s
    "loop_invariant_body.md",                                // 1.2s
    "loop_invariant_conversion_side_condition_false_at_the_back_edge_is_refused.md", // 0.8s
    "loop_invariant_conversion_side_condition_is_assumed_at_the_head.md", // 1.9s
    "loop_invariant_growing_viewable_prefix_bounded_by_its_views_clause.md", // 4.6s
    "loop_invariant_old_model_when_the_unfold_precedes_execution.md", // 2.2s
    "loop_invariant_on_a_symbolic_cell_is_not_free.md",      // 1.5s
    "loop_invariant_states_a_growing_viewable_prefix.md",    // 4.8s
    "loop_invariant_viewable_prefix_owes_its_span_at_the_back_edge.md", // 4.2s
    "loop_invariant_viewable_range_false_at_the_back_edge_is_refused.md", // 1.4s
    "loop_local_pointer_element_types.md",                   // 1.1s
    "loop_measure_reads_a_model_function.md",                // 1.9s
    "loop_measure_reads_a_nat_model_function.md",            // 0.8s
    "loop_node_link_frames_across_parent_link_store.md",     // 2.3s
    "loop_node_link_rejects_store_to_same_link.md",          // 4.6s
    "loop_old_count_invariant.md",                           // 1.2s
    "loop_otherwise.md",                                     // 0.8s
    "loop_owns_preserves_symbolic_index.md",                 // 2.2s
    "loop_preservation_case_after_step.md",                  // 1.4s
    "loop_preserve_branch.md",                               // 2.0s
    "loop_preserve_branch_tactic.md",                        // 3.6s
    "loop_preserve_decided_branch_expands.md",               // 5.3s
    "loop_preserve_if_reads_match_binding.md",               // 3.9s
    "loop_quantified_memory_invariant.md",                   // 1.9s
    "loop_quantified_memory_invariant_rejects_false.md",     // 0.6s
    "loop_ranks_a_body_ending_in_a_branch.md",               // 2.6s
    "loop_rejects_stale_address_escaped_local.md",           // 1.5s
    "loop_rejects_stale_pre_loop_store.md",                  // 1.6s
    "loop_resource_backing_range_fold_after_write.md",       // 2.7s
    "loop_resource_binder_field_is_not_a_local.md",          // 2.3s
    "loop_resource_lifetime_join.md",                        // 1.6s
    "loop_return_closes_in_preserve_arm.md",                 // 2.1s
    "loop_return_rejects_false_arm_closer.md",               // 2.1s
    "loop_sorted_range_invariant.md",                        // 1.3s
    "loop_stable_invariant_export.md",                       // 2.0s
    "loop_static_not_havoced_rejected.md",                   // 2.6s
    "loop_stdlib_permutation_invariant.md",                  // 1.1s
    "loop_token_lifetime_join.md",                           // 1.3s
    "machine_integer_quantified_arithmetic.md",              // 0.7s
    "match_binder_captures_havocked_local.md",               // 2.1s
    "memcmp_orders_after_equal_prefix.md",                   // 0.6s
    "memcmp_reads_two_viewed_buffers.md",                    // 0.8s
    "memcpy_reads_a_viewed_or_borrowed_source.md",           // 0.7s
    "memcpy_write_separation.md",                            // 0.8s
    "memory_predicate_explicit_frame.md",                    // 1.6s
    "memory_reading_lambdas.md",                             // 2.1s
    "memset_converts_fill_value_to_unsigned_char.md",        // 0.6s
    "model_field_across_a_loop_without_an_invariant.md",     // 1.9s
    "model_pointer_fields_keep_object_class.md",             // 1.0s
    "model_pointer_fold_rejects_wrong_back_link.md",         // 1.6s
    "model_pointer_fold_rejects_wrong_field_value.md",       // 1.9s
    "model_pointer_numeric_address_does_not_preserve_view.md", // 1.3s
    "model_pointer_provisional_recursion_accepts_typed_actuals.md", // 0.7s
    "modeled_pthread_held_balanced_loop.md",                 // 1.9s
    "modeled_pthread_iteration_local_mutex.md",              // 1.9s
    "modeled_pthread_local_job_external_output.md",          // 0.5s
    "modeled_pthread_mutex_parent_interference.md",          // 0.5s
    "modeled_pthread_mutex_parent_interference_rejects_stale.md", // 0.8s
    "modeled_pthread_reinitialized_loop.md",                 // 1.4s
    "modeled_pthread_unbalanced_loop_rejected.md",           // 1.3s
    "modular_call_requirement_indexes_footprint.md",         // 1.1s
    "mutex_counter_double_increment_rejected.md",            // 1.4s
    "mutex_counter_doubled_contribution_rejected.md",        // 1.2s
    "mutex_counter_total_before_second_join_rejected.md",    // 1.6s
    "mutex_counter_worker.md",                               // 0.5s
    "mutex_helper_transfers.md",                             // 0.8s
    "mutex_parity_direct.md",                                // 3.5s
    "mutex_parity_direct_rejects_missing_transitions.md",    // 0.6s
    "mutex_parity_direct_rejects_unheld_unlock.md",          // 0.6s
    "mutex_parity_rejects_unguarded_unlock.md",              // 0.6s
    "mutex_resource_quantity_requires_conservation.md",      // 3.8s
    "mutex_use_mixed.md",                                    // 0.7s
    "named_contract_outputs_retain_the_callers_frame.md",    // 0.7s
    "named_contract_value_parameter_contract_refinement_theorem_rejects_another_value.md", // 4.4s
    "named_contract_value_parameter_execution_theorem_rejects_another_source_value.md", // 1.4s
    "named_contract_value_parameter_execution_theorem_rejects_another_value.md", // 1.1s
    "named_contract_value_parameter_refinement_theorem_rejects_another_value.md", // 2.8s
    "named_transport_carries_guarded_definedness.md",        // 0.6s
    "narrow_comparisons_after_rewrite.md",                   // 0.9s
    "narrowing_from_wide_sources_into_bytes_and_shorts.md",  // 1.0s
    "native_view_prefix_narrowing_extra_byte_rejected.md",   // 0.5s
    "native_view_window_extra_byte_rejected.md",             // 0.6s
    "native_view_window_underflow_rejected.md",              // 0.5s
    "natural_goto_conditional_backedge.md",                  // 0.7s
    "natural_goto_exit_label.md",                            // 0.8s
    "natural_goto_forward_exit_and_return.md",               // 0.8s
    "natural_goto_forward_exit_differing_states.md",         // 0.7s
    "natural_goto_forward_exit_differing_states_false_contract.md", // 0.8s
    "natural_goto_forward_exit_multiple_edges_rejects_wrong_result.md", // 0.8s
    "natural_goto_forward_exit_multiple_edges_state.md",     // 0.7s
    "natural_goto_forward_exit_rejects_undefined_return.md", // 0.7s
    "natural_goto_forward_exit_rejects_wrong_result.md",     // 0.8s
    "natural_goto_forward_exit_requires_exit_execution.md",  // 0.7s
    "natural_goto_forward_exit_state.md",                    // 0.7s
    "natural_goto_multiple_backedges.md",                    // 1.1s
    "natural_goto_multiple_exit_labels.md",                  // 0.7s
    "nested_field_aliases_keep_post_call_scalar_reads.md",   // 0.7s
    "nested_loop_enclosing_mark.md",                         // 2.4s
    "nested_loop_inner_mark_stays_local.md",                 // 1.2s
    "nested_loop_measure_rejected.md",                       // 3.5s
    "nested_loop_preserve.md",                               // 1.6s
    "nested_loop_return_checks_postcondition.md",            // 3.4s
    "nested_loop_return_survives_outer_backedge.md",         // 3.4s
    "normalize_using_adds_a_constant_element_offset_by_a_cited_integer_sum.md", // 1.3s
    "null_assignment_preserves_loop_object_class_join.md",   // 0.7s
    "observe_quantity_positive_without_search.md",           // 0.5s
    "observe_saved_pointer_memory_range.md",                 // 0.5s
    "open_named_resource_requires_restoration.md",           // 0.7s
    "open_scope_model_match_rejects_bad_arm.md",             // 0.7s
    "operand_bounds_define_a_bounded_difference_and_product.md", // 1.1s
    "operation_and_excluded_bounds_in_solve_using.md",       // 0.7s
    "order_bounds_place_a_store_off_a_constant_element.md",  // 1.2s
    "order_chains_of_three_facts_close.md",                  // 1.6s
    "ordered_index_sibling_store_rejects_stale_read.md",     // 0.9s
    "ordinary_helper_forwards_an_empty_slot_batch.md",       // 0.7s
    "outcome_apply_obligations.md",                          // 0.9s
    "owned_pieces_that_may_not_abut_do_not_rejoin.md",       // 0.7s
    "owned_range_fact_across_a_preserved_pointer_call.md",   // 1.2s
    "packed_model_pointer_loop_object_class.md",             // 1.4s
    "packed_parent_transport_across_aliased_metadata.md",    // 0.9s
    "packed_pointer_loop_object_class.md",                   // 1.5s
    "padded_field_scalar_call_restores_ownership.md",        // 0.6s
    "pointer_cursor_loop_expansion.md",                      // 5.2s
    "pointer_integer_round_trips_across_a_call.md",          // 0.7s
    "pointer_integer_round_trips_across_a_separate_store.md", // 0.6s
    "pointer_nonself_fact_requires_evidence.md",             // 0.8s
    "pointer_read_alias_rejects_self_links.md",              // 3.1s
    "pointer_store_through_loaded_alias_rejects_overwrite.md", // 0.8s
    "pool_control_call_frames_derived_bounds.md",            // 0.9s
    "population_call_drops_the_cached_body_cell.md",         // 1.1s
    "population_conservation_local_mutex_bad_increment.md",  // 3.1s
    "population_consumption_missing_contract.md",            // 2.7s
    "population_consumption_nested_overconsume.md",          // 6.4s
    "population_consumption_repeated.md",                    // 3.5s
    "population_consumption_wrong_increment.md",             // 2.5s
    "population_mutex_hidden_unit_at_release.md",            // 1.3s
    "population_private_body_borrow_separation.md",          // 0.6s
    "population_symbolic_increment_bounded.md",              // 1.3s
    "post_call_constant_equality_proves_a_bound.md",         // 0.9s
    "post_call_constant_equality_refuses_a_false_bound.md",  // 0.6s
    "preserve_apply_names_its_missing_viewable.md",          // 3.6s
    "preserve_empty_arm_reports_frontier.md",                // 0.6s
    "preserve_runs_the_rest_of_the_body.md",                 // 1.4s
    "printf_and_fprintf_share_the_streams_write_history.md", // 7.9s
    "printf_refuses_a_format_that_converts.md",              // 0.9s
    "private_state_mutation_reset.md",                       // 1.3s
    "produced_population_count_in_ensured_predicate.md",     // 0.6s
    "proof_branch_continuation.md",                          // 0.6s
    "proof_branch_memory_continuation.md",                   // 0.6s
    "proof_branch_nested_resource_scope.md",                 // 0.6s
    "proof_interface_pointer_read_congruence_after_loop.md", // 1.8s
    "proof_match_arm_fact_survives_sibling_write.md",        // 0.7s
    "proof_match_payload_identity_rejects_overwrite.md",     // 2.0s
    "pure_arithmetic_affine.md",                             // 0.5s
    "pure_arithmetic_bounded_operations.md",                 // 1.4s
    "pure_arithmetic_rejects_nonlinear.md",                  // 1.5s
    "pure_arithmetic_retains_a_rewritten_fold_goal.md",      // 0.8s
    "pure_induction_countdown.md",                           // 1.1s
    "pure_induction_countdown_explicit.md",                  // 1.0s
    "pure_induction_guarded_offset.md",                      // 2.1s
    "pure_induction_is_explicit.md",                         // 0.6s
    "pure_induction_keeps_other_parameters_fixed.md",        // 1.0s
    "pure_induction_mutual_conjunction.md",                  // 1.1s
    "pure_induction_preserves_requirements.md",              // 0.9s
    "pure_induction_rejects_larger_measure.md",              // 0.8s
    "pure_induction_two_step.md",                            // 1.1s
    "pure_pointer_projection_preserves_loop_resource_spelling.md", // 1.0s
    "pure_recursive_function_in_invariant.md",               // 1.8s
    "pure_result_observation_call_requirement_refuses_false.md", // 1.5s
    "qualified_pointer_global_store_rejects_old_value.md",   // 0.5s
    "quantified_disjoint_array_store_frame.md",              // 0.8s
    "quantified_frame_carries_a_bound_fact_to_the_current_state.md", // 0.7s
    "quantified_frame_carries_a_separated_array_past_a_store_and_a_call.md", // 2.0s
    "quantified_frame_rejects_a_call_writing_the_range.md",  // 0.8s
    "quantified_frame_rejects_a_changed_base_pointer.md",    // 2.8s
    "quantified_frame_rejects_a_freed_array.md",             // 0.8s
    "quantified_frame_rejects_a_guard_past_the_separated_range.md", // 2.1s
    "quantified_frame_rejects_a_guard_the_store_widens.md",  // 1.8s
    "quantified_frame_rejects_a_loop_that_writes_the_range.md", // 2.8s
    "quantified_frame_rejects_a_read_past_the_separated_range.md", // 3.4s
    "quantified_frame_rejects_a_second_store_the_guard_admits.md", // 1.1s
    "quantified_frame_rejects_a_store_the_guard_admits.md",  // 1.4s
    "quantified_frame_rejects_a_wide_store_beside_the_excluded_cell.md", // 2.2s
    "quantified_frame_rejects_an_unseparated_alias.md",      // 0.9s
    "quantified_frame_rejects_states_across_a_store_in_either_order.md", // 1.5s
    "range_helpers_over_memory.md",                          // 0.5s
    "rb_at_rejects_wrong_color_bit.md",                      // 0.8s
    "rb_at_rejects_wrong_parent_word.md",                    // 2.5s
    "rb_change_child_rejects_wrong_slot.md",                 // 0.6s
    "reads_of_one_kind_at_one_address_stay_equal.md",        // 0.5s
    "recursive_call_precondition_bounds_a_decremented_argument.md", // 1.0s
    "recursive_call_precondition_refuses_a_decremented_lower_bound.md", // 0.6s
    "recursive_walk_survives_unrelated_store.md",            // 0.8s
    "refcount_releaser_cannot_free_shared_object.md",        // 0.9s
    "region_relative_index_read.md",                         // 3.0s
    "reloaded_local_pointer_impossible.md",                  // 0.5s
    "repeated_child_retains_cannot_overflow_the_count.md",   // 1.1s
    "repeated_child_retains_require_enough_count_capacity.md", // 0.7s
    "repeated_loop_verified_rules.md",                       // 2.2s
    "resource_child_pure_arguments_write_footprint.md",      // 1.2s
    "resource_field_memory_endpoint_rejects_out_of_bounds_fold.md", // 1.1s
    "resource_fold_rejects_wrong_copied_packed_parent.md",   // 12s
    "resource_match_quantified_fact_rejects_changed_load.md", // 2.0s
    "resource_model_byte_pointer_theorem_arguments.md",      // 0.9s
    "resource_model_pointer_theorem_rejects_wrong_elements.md", // 0.8s
    "resource_pattern_counts_cross_contracts.md",            // 1.1s
    "resource_summary_splits_symbolic_write_range.md",       // 0.8s
    "resource_unfold_reads_the_opened_field.md",             // 15s
    "resource_witness_fold_infers_origin.md",                // 0.6s
    "result_parameter_false_cast_postcondition.md",          // 0.6s
    "result_parameter_false_field_postcondition.md",         // 1.6s
    "retained_loop_metadata_transport_crosses_a_separated_store.md", // 1.9s
    "retained_shift_bounds_have_explicit_certificates.md",   // 2.5s
    "return_population_rejects_unupdated_sibling.md",        // 1.0s
    "returned_allocation_pass_through_keeps_cleanup_authority.md", // 0.5s
    "returned_pointer_may_alias_a_global.md",                // 0.8s
    "returned_pointer_to_a_caller_local_may_alias_it.md",    // 0.6s
    "rewrite_heap_alias_rejects_stale_payload.md",           // 0.8s
    "rewrite_pointer_into_a_shifted_byte_view.md",           // 0.5s
    "saved_memory_bases_keep_current_indices.md",            // 1.0s
    "saved_memory_indices_do_not_freeze_at_entry.md",        // 0.5s
    "scalar_induction_keeps_fixed_integer_parameters.md",    // 1.9s
    "scoped_conversion_obligations_reject_an_unsafe_binder.md", // 1.9s
    "separate_symbolic_unwritten_read.md",                   // 2.0s
    "separation_restricts_equal_array_bases.md",             // 2.1s
    "sequential_branches_join_with_branch_ensuring.md",      // 2.5s
    "sequential_conditional_expressions_join_with_a_proof_if.md", // 2.7s
    "shared_heap_double_release_rejected.md",                // 2.0s
    "shift_count_mask_requires_a_valid_upper_bound.md",      // 1.0s
    "shifted_copy_effect_uses_covering_separate.md",         // 2.9s
    "shifted_loop_effect_preserves_prefix.md",               // 2.0s
    "signed_byte_swap_uses_a_selected_frame.md",             // 0.8s
    "signed_int32_certificate_composition.md",               // 1.9s
    "signed_interval_negation_requires_the_selected_bound.md", // 0.5s
    "signed_loop_certificate_keeps_its_native_type.md",      // 1.9s
    "signed_narrowed_length_arithmetic.md",                  // 2.9s
    "signed_neighbour_indexes_stay_apart.md",                // 1.8s
    "signed_product_lower_guard_requires_the_reversed_order.md", // 2.0s
    "signed_product_needs_guard_for_the_actual_divisor.md",  // 2.0s
    "snprintf_call_map_names_a_local_c_string.md",           // 1.1s
    "snprintf_copies_a_c_string_the_caller_views.md",        // 0.7s
    "snprintf_counts_the_characters_that_do_not_fit.md",     // 1.3s
    "snprintf_states_its_result_sign_and_terminator.md",     // 1.7s
    "snprintf_with_a_literal_format_states_each_character.md", // 2.6s
    "solve_bounds_an_unsigned_quotient_by_its_operand.md",   // 2.7s
    "solve_closes_a_64_bit_order_chain.md",                  // 0.6s
    "solve_closes_an_equality_from_opposite_bounds_at_every_width.md", // 1.1s
    "solve_composes_a_pointer_field_chain_across_a_call.md", // 0.6s
    "solve_defined_count_after_a_zero_summand.md",           // 1.3s
    "solve_does_not_read_an_unforced_condition.md",          // 0.6s
    "solve_does_not_weaken_a_guarded_universal_to_a_wider_range.md", // 1.4s
    "solve_evaluates_a_recursive_function_over_known_constructors.md", // 1.0s
    "solve_follows_a_bound_to_another_variable.md",          // 2.6s
    "solve_native_view_prefix_discards_redundant_selected_bounds.md", // 1.1s
    "solve_observes_a_nested_sum_under_integer_arithmetic.md", // 2.6s
    "solve_observes_a_product_by_a_constant.md",             // 4.7s
    "solve_observes_an_operation_term_by_term.md",           // 1.1s
    "solve_plans_a_narrow_comparison_through_its_operation_identity.md", // 3.8s
    "solve_proves_an_implication_whose_consequent_needs_the_solver.md", // 0.6s
    "solve_proves_an_in_range_machine_sum_is_its_integer_sum.md", // 0.5s
    "solve_proves_element_addresses_distinct_from_their_indices.md", // 1.1s
    "solve_proves_wide_bounds_and_let_bound_increments.md",  // 3.9s
    "solve_reads_a_bound_from_a_negated_branch_condition.md", // 1.0s
    "solve_reads_a_bound_inside_a_requires_conjunction.md",  // 1.1s
    "solve_reads_a_call_postcondition_for_a_machine_bound.md", // 0.5s
    "solve_reads_a_condition_out_of_a_definition.md",        // 2.8s
    "solve_reads_a_narrowing_cast_inside_its_range.md",      // 1.6s
    "solve_reads_a_shift_bound_from_a_negated_condition.md", // 0.5s
    "solve_reads_a_widening_cast_as_its_operand.md",         // 0.6s
    "solve_reads_bounds_before_function_exit.md",            // 2.4s
    "solve_reads_definitions_and_constructor_equations.md",  // 0.6s
    "solve_refuses_a_bound_the_conjunction_does_not_give.md", // 0.7s
    "solve_refuses_an_addition_that_may_overflow.md",        // 0.6s
    "solve_spells_a_replaced_value_at_function_entry.md",    // 0.6s
    "sort3_permutation_predicate.md",                        // 1.3s
    "stated_range_carries_its_span_bound.md",                // 2.5s
    "statement_regions_count_the_arms_of_an_if_together.md", // 1.4s
    "statement_regions_name_points_of_statements_as_written.md", // 1.2s
    "statement_regions_reach_a_loop_body.md",                // 1.8s
    "static_local_array_requirement_stated_explicitly.md",   // 1.0s
    "static_scalar_locals.md",                               // 0.7s
    "static_subobject_pointer_initializers_cross_file.md",   // 0.6s
    "step_nested_branches.md",                               // 0.5s
    "step_value_map_takes_the_frontier_call.md",             // 1.5s
    "store_geometry_uses_explicit_order_and_transport.md",   // 0.5s
    "sweep_maintains_a_zero_unmarked_count.md",              // 2.8s
    "sweep_prefix_survives_its_endpoint_store.md",           // 2.9s
    "symbolic_index_store_keeps_ordered_cell.md",            // 0.9s
    "symbolic_owned_pieces_caller_must_prove_separation.md", // 0.9s
    "the_back_edge_closes_a_guarded_member_by_intro.md",     // 11s
    "the_back_edge_ranks_a_reassigned_parameter.md",         // 1.2s
    "the_back_edge_splits_a_conjunction_chain_first.md",     // 2.1s
    "token_quantity_returned_from_two_separate_units.md",    // 33s
    "tracing_a_nonlinear_bound_is_the_refused_goal.md",      // 0.7s
    "tracing_an_intermediate_goal_proves_the_bound.md",      // 0.7s
    "transport_model_pointer_binding_rejects_changed_cell.md", // 1.5s
    "transport_narrows_a_view_to_a_window_that_starts_at_a_sum.md", // 1.2s
    "transport_refuses_a_window_that_starts_at_a_sum_without_its_end_bound.md", // 0.9s
    "two_call_memory_facts_support_arithmetic.md",           // 3.2s
    "uint32_order_lemmas_state_single_unsigned_steps.md",    // 1.1s
    "uint64_measure_induction_counts_a_range_fold.md",       // 0.9s
    "uint64_measure_induction_keeps_the_full_width.md",      // 0.7s
    "uint64_partial_restoration_bounds.md",                  // 0.7s
    "uint64_read_after_resource_call_rejects_changed_tag.md", // 2.4s
    "uint8_fill_loop_range.md",                              // 1.9s
    "uint8_loop_invariant_pure_function.md",                 // 2.6s
    "uint8_write_i_read_j.md",                               // 1.1s
    "unfold_child_scalar_identity_rejects_overwrite.md",     // 3.0s
    "unfold_fold_does_not_assume_nonnegative_cells.md",      // 3.2s
    "unfold_fold_function_appends_last_cell.md",             // 0.7s
    "unfold_fold_int32_uses_ordinary_obligations.md",        // 1.9s
    "unfold_fold_memory_body_append.md",                     // 1.2s
    "unfold_fold_nonempty_is_not_assumed_empty.md",          // 2.2s
    "unfold_fold_selected_guards_generate_remaining_obligations.md", // 0.8s
    "unfold_fold_uint64_uses_ordinary_obligations.md",       // 0.8s
    "unfold_names_a_witness_for_a_fold_body_fact.md",        // 2.7s
    "unfold_parent_alias_before_child_read.md",              // 0.7s
    "unfolded_last_cell_does_not_cross_a_later_store.md",    // 0.8s
    "uninitialized_destination_beside_a_viewed_source.md",   // 4.6s
    "uninitialized_input_does_not_publish_definedness.md",   // 0.5s
    "unsigned_integer_bridges.md",                           // 0.8s
    "user_tactic_at_return.md",                              // 0.9s
    "user_tactic_produced_cell_supplies_named_output.md",    // 1.1s
    "user_tactic_requires_obligations.md",                   // 1.2s
    "using_lists_accept_premises_that_hold_without_facts.md", // 0.8s
    "variable_arguments_are_promoted.md",                    // 0.7s
    "viewable_range_requirement_stated_explicitly.md",       // 2.0s
    "viewable_requirement_supports_a_narrower_span.md",      // 2.1s
    "viewed_memory_call_frame_rejects_an_iterated_owner_borrow.md", // 0.8s
    "whole_struct_lends_nested_and_array_fields.md",         // 0.5s
    "widened_unsigned_sum_bounds.md",                        // 1.6s
    "widened_unsigned_sum_bounds_fail.md",                   // 0.6s
    "wrapping_arithmetic_written_as_integer_arithmetic_is_refused.md", // 0.5s
];

/// The hidden prerequisite ratchet (`docs/internals/testing.md`): count the
/// prerequisites simple statement checking derived by a search the proof does
/// not retain, over the whole unfiltered corpus, by route and top rule. A
/// count may only fall, and it is zero.
const HIDDEN_PREREQUISITE_BASELINE: &[((HiddenPrerequisiteRoute, &str), usize)] = &[];

/// Every C++ mdtest's checked-in import under `mdtests/cpp-imports` is what
/// the pinned exporter produces now, and no import outlives its mdtest. The
/// other mdtests load these imports without a compiler; this test needs the
/// exporter, so it runs where `CLICK_CPP_EXPORTER` names one.
/// `scripts/refresh-cpp-imports.sh` rewrites them.
#[test]
fn cpp_mdtest_imports_match_the_pinned_exporter() {
    let Some(exporter) = std::env::var_os("CLICK_CPP_EXPORTER").map(PathBuf::from) else {
        println!("SKIPPING C++ import freshness: CLICK_CPP_EXPORTER is not set");
        return;
    };
    let refresh = std::env::var_os(REFRESH_CPP_IMPORTS).is_some();
    let mdtests_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("mdtests");
    let imports_dir = mdtests_dir.join("cpp-imports");
    let mut fixtures = fs::read_dir(&mdtests_dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "md"))
        .filter_map(|path| {
            let mdtest = read_mdtest(&path).ok()?;
            mdtest.cpp_source.is_some().then_some((path, mdtest))
        })
        .collect::<Vec<_>>();
    fixtures.sort_by(|left, right| left.0.cmp(&right.0));
    let exported = std::thread::scope(|scope| {
        let handles = fixtures
            .iter()
            .map(|(path, mdtest)| {
                let exporter = &exporter;
                scope.spawn(move || {
                    (
                        path.clone(),
                        mdtest
                            .cpp_source
                            .as_ref()
                            .unwrap()
                            .import_directory
                            .clone()
                            .unwrap(),
                        export_cpp_mdtest_import(mdtest, exporter),
                    )
                })
            })
            .collect::<Vec<_>>();
        handles
            .into_iter()
            .map(|handle| handle.join().unwrap())
            .collect::<Vec<_>>()
    });
    let mut problems = Vec::new();
    let mut kept = std::collections::BTreeSet::new();
    for (path, directory, files) in exported {
        let files = files.unwrap_or_else(|error| panic!("`{}`: {error}", path.display()));
        kept.insert(directory.clone());
        let checked_in = checked_in_files(&directory);
        if same_import(&checked_in, &files) {
            continue;
        }
        if refresh {
            let _ = fs::remove_dir_all(&directory);
            for (relative, bytes) in &files {
                let destination = directory.join(relative);
                fs::create_dir_all(destination.parent().unwrap()).unwrap();
                fs::write(destination, bytes).unwrap();
            }
        } else {
            problems.push(format!(
                "`{}`: {}",
                directory.display(),
                first_import_difference(&checked_in, &files)
            ));
        }
    }
    for entry in fs::read_dir(&imports_dir).into_iter().flatten() {
        let directory = entry.unwrap().path();
        if !kept.contains(&directory) {
            if refresh {
                fs::remove_dir_all(&directory).unwrap();
            } else {
                problems.push(format!("`{}` (no mdtest uses it)", directory.display()));
            }
        }
    }
    assert!(
        problems.is_empty(),
        "C++ mdtest imports differ from the pinned exporter's; run scripts/refresh-cpp-imports.sh:\n  {}",
        problems.join("\n  ")
    );
}

#[test]
fn mdtests() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mdtests_dir = manifest_dir.join("mdtests");
    let mut paths = fs::read_dir(&mdtests_dir)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", mdtests_dir.display()))
        .map(|entry| {
            entry
                .unwrap_or_else(|error| panic!("failed to read mdtest directory entry: {error}"))
                .path()
        })
        // Imported theorem bodies are interfaces to their importers. Run each
        // local Click library as its own entry so the gate checks those bodies.
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "md" || extension == "click")
        })
        .collect::<Vec<_>>();
    let named_filter = if let Ok(filter) = std::env::var("MDTEST_FILTER") {
        // A whole file name selects just that file; anything else selects
        // every file whose name contains it.
        let exact = filter.ends_with(".md");
        paths.retain(|path| {
            path.file_name().is_some_and(|name| {
                let name = name.to_string_lossy();
                if exact {
                    name == filter
                } else {
                    name.contains(&filter)
                }
            })
        });
        true
    } else {
        false
    };
    let quick_solve_only = std::env::var_os(QUICK_SOLVE_ONLY).is_some();
    if quick_solve_only {
        paths.retain(|path| {
            path.extension().is_some_and(|extension| extension == "md")
                && read_mdtest(path)
                    .unwrap_or_else(|error| panic!("{error}"))
                    .quick_solve
        });
    }
    let filtered = named_filter || quick_solve_only;
    if !filtered && std::env::var_os(RUN_QUARANTINED).is_none() {
        paths.retain(|path| {
            let name = path.file_name().and_then(|name| name.to_str());
            let quarantine = name.and_then(|name| {
                QUARANTINED
                    .iter()
                    .find(|(quarantined, _)| *quarantined == name)
            });
            match quarantine {
                Some((name, reason)) => {
                    println!("SKIPPING quarantined mdtest `{name}`: {reason}");
                    false
                }
                None => true,
            }
        });
    }
    // A gate run leaves the slow fixtures to the nightly run.
    let skipped_nightly = !filtered && std::env::var_os("CLICK_NIGHTLY").is_none() && {
        for name in NIGHTLY {
            assert!(
                mdtests_dir.join(name).is_file(),
                "nightly mdtest `{name}` does not exist; remove it from NIGHTLY in tests/mdtests.rs"
            );
        }
        let before = paths.len();
        paths.retain(|path| {
            let name = path.file_name().and_then(|name| name.to_str());
            !name.is_some_and(|name| NIGHTLY.contains(&name))
        });
        println!(
            "SKIPPING {} nightly mdtests (NIGHTLY in tests/mdtests.rs)",
            before - paths.len()
        );
        true
    };
    paths.sort();
    // CI splits the corpus across jobs to stay inside the gate's time
    // budget: `MDTEST_PARTITION=k/n` keeps every n-th file from the k-th,
    // over the sorted names, so the shards cover the corpus exactly once.
    let partitioned = if let Ok(partition) = std::env::var("MDTEST_PARTITION") {
        let (shard, total) = partition
            .split_once('/')
            .and_then(|(shard, total)| {
                Some((shard.parse::<usize>().ok()?, total.parse::<usize>().ok()?))
            })
            .filter(|(shard, total)| (1..=*total).contains(shard))
            .unwrap_or_else(|| {
                panic!("MDTEST_PARTITION must be `k/n` with 1 <= k <= n, got `{partition}`")
            });
        let mut index = 0;
        paths.retain(|_| {
            index += 1;
            (index - 1) % total == shard - 1
        });
        true
    } else {
        false
    };
    // Without its nightly fixtures the corpus is partial, as in a partition:
    // the hidden prerequisite ratchet still catches a rise but cannot see a
    // fall.
    let partial = partitioned || skipped_nightly;

    assert!(
        !paths.is_empty(),
        "expected at least one mdtest in `{}`",
        mdtests_dir.display()
    );

    // Verify files on every core. Tactic correctness is enforced by
    // deterministic work budgets, not by how much CPU time happens to be
    // available to each file, so concurrency cannot change a verdict. Peak
    // memory stays small: on 2026-09-11 the whole corpus peaked at 171 MB
    // serially and 291 MB on 8 workers.
    let _ = instrumentation::take_hidden_prerequisite_census();
    let _ = instrumentation::take_backwards_memory_derivation_census();
    let workers = std::thread::available_parallelism().map_or(1, usize::from);
    let failures = limits::run_parallel(&paths, workers, |path| run_mdtest_in_thread(path));
    let hidden_prerequisites = instrumentation::take_hidden_prerequisite_census();
    // Which producers still end a step on a state older than itself, so
    // that the step is recorded on no history. A knowledge-losing forget
    // cannot: its mark makes the result a node no earlier state can be
    // (`SymbolicMemory::mark_forgotten_from`). Anything else here is a producer
    // whose steps are invisible to every history-based rule, and this line
    // is how a corpus run names it.
    eprintln!(
        "backwards memory derivations over the corpus: {:?}",
        instrumentation::take_backwards_memory_derivation_census()
    );
    if failures.is_empty() {
        if !filtered
            && std::env::var_os(RUN_QUARANTINED).is_none()
            && let Some(mismatch) = instrumentation::hidden_prerequisite_census_mismatch(
                &hidden_prerequisites,
                HIDDEN_PREREQUISITE_BASELINE,
                partial,
            )
        {
            panic!("hidden prerequisite ratchet (tests/mdtests.rs baselines):\n{mismatch}");
        }
        return;
    }

    let mut message = format!("{} of {} mdtests failed:\n", failures.len(), paths.len());
    for (index, diagnostics) in failures {
        message.push_str(&format!("\n`{}` {diagnostics}\n", paths[index].display()));
    }
    panic!("{message}");
}

fn run_mdtest_in_thread(path: &Path) -> Result<(), String> {
    let path = path.to_path_buf();
    let thread_name = path.file_stem().and_then(|name| name.to_str()).map_or_else(
        || "click-mdtest".to_string(),
        |name| format!("mdtest-{name}"),
    );
    // One line as each fixture starts and one as it finishes, on stderr so
    // the gate can stream them: a stall shows as a started fixture that
    // never finishes, and a slow fixture is visible while it runs, not only
    // in the total afterwards.
    let name = path.display().to_string();
    eprintln!("mdtest `{name}` started");
    let started = std::time::Instant::now();
    let result = limits::spawn("mdtest verifier", thread_name, move || {
        run_mdtest_attempt(&path)
    })?;
    let seconds = started.elapsed().as_secs_f64();
    eprintln!(
        "mdtest `{name}` {} in {seconds:.2}s",
        if result.is_ok() { "passed" } else { "failed" },
    );
    click::nightly_report::record(
        "mdtests",
        &click::nightly_report::NightlyResult {
            kind: "mdtest",
            name: path_file_name(&name),
            passed: result.is_ok(),
            seconds,
            message: result.as_ref().err().map(String::as_str),
        },
    );
    result
}

/// The file name the report's `MDTEST_FILTER=<name>` selects.
fn path_file_name(path: &str) -> &str {
    path.rsplit('/').next().unwrap_or(path)
}

fn run_mdtest_attempt(path: &Path) -> Result<(), String> {
    // A calibration run measures every fixture unclipped, so the pinned
    // budgets below step aside with the defaults.
    let budgets_disabled = std::env::var_os("CLICK_DISABLE_TACTIC_BUDGETS").is_some();
    if !budgets_disabled
        && path
            .file_name()
            .is_some_and(|name| name == "bubble_sort3_loop_permutation.md")
    {
        // This is the former load-sensitive clock canary. Its measured
        // maxima are simple 146, smart 21,090, and control 42,169 work
        // units. Pin all three classes below 100,000 so machine load
        // cannot change the result.
        let limits = instrumentation::TacticWorkLimits {
            simple: BUBBLE_SORT3_WORK_LIMIT,
            smart: BUBBLE_SORT3_WORK_LIMIT,
            control: BUBBLE_SORT3_WORK_LIMIT,
        };
        return instrumentation::with_tactic_work_limits(limits, || run_mdtest(path));
    }
    if !budgets_disabled
        && path
            .file_name()
            .is_some_and(|name| name == "explicit_preserve_failure_is_prompt.md")
    {
        return instrumentation::with_tactic_work_limits(
            instrumentation::TacticWorkLimits {
                simple: PROMPT_EXPLICIT_FRAME_FAILURE_WORK_LIMIT,
                control: PROMPT_EXPLICIT_FRAME_FAILURE_WORK_LIMIT,
                ..instrumentation::TacticWorkLimits::default()
            },
            || run_mdtest(path),
        );
    }
    run_mdtest(path)
}

fn timed_mdtest_phase<T>(path: &Path, phase: &str, run: impl FnOnce() -> T) -> T {
    let started = std::env::var_os("CLICK_MDTEST_PHASE_TIMINGS")
        .is_some()
        .then(std::time::Instant::now);
    let result = run();
    if let Some(started) = started {
        eprintln!(
            "mdtest phase `{}` {phase} {:.6}s",
            path.display(),
            started.elapsed().as_secs_f64()
        );
    }
    result
}

fn run_mdtest(path: &Path) -> Result<(), String> {
    if path
        .extension()
        .is_some_and(|extension| extension == "click")
    {
        let source = fs::read_to_string(path)
            .map_err(|error| format!("failed to read `{}`: {error}", path.display()))?;
        let project = read_click_project(path, &source)?;
        let inputs = read_verification_inputs_for_project(path, &source, &project)?;
        let (_, verification) =
            click::surface::verify_project_with_summary(&project, &inputs.program_inputs())
                .map_err(|error| error.report())?;
        return verification.map(|_| ()).map_err(|error| error.report());
    }
    let mdtest = timed_mdtest_phase(path, "read", || read_mdtest(path))?;
    let click_source = mdtest
        .click_source
        .as_deref()
        .ok_or_else(|| format!("`{}` is missing a ```click block", path.display()))?;
    let inputs = timed_mdtest_phase(path, "prepare-inputs", || prepare_mdtest_inputs(&mdtest))?;
    let expectation = mdtest
        .expectation
        .as_ref()
        .ok_or_else(|| format!("`{}` is missing a ```expect block", path.display()))?;

    let project = timed_mdtest_phase(path, "load-project", || {
        read_mdtest_project_if_needed(path, click_source, &inputs)
    })?;
    let verify = || -> Result<(), ClickError> {
        match (&inputs, &project) {
            (VerificationInput::Bundle(sources), Some(project)) => {
                verify_c_project(project, &source_refs(sources)).map(|_| ())
            }
            (VerificationInput::Bundle(sources), None) => {
                verify_c_sources(click_source, &source_refs(sources)).map(|_| ())
            }
            (VerificationInput::PreparedProgram(import), Some(project)) => {
                verify_program_prepared_project(project, import).map(|_| ())
            }
            (VerificationInput::PreparedProgram(_), None) | (VerificationInput::Prepared(_), _) => {
                unreachable!("every prepared mdtest input reads a Click project")
            }
        }
    };

    if mdtest.checked_only {
        let result = timed_mdtest_phase(path, "verify", || {
            click::surface::without_proof_search(|| {
                verify().map_err(|error| {
                    click::surface::display_source_names(error.message()).into_owned()
                })
            })
        });
        return check_rendered_expectation(path, expectation, result);
    }

    let (result, samples) = timed_mdtest_phase(path, "verify", || {
        tactic_work::measure(mdtest.quick_solve, verify)
    });
    if !samples.is_empty() {
        let line_offset = mdtest.click_start_line.saturating_sub(1);
        let relative = path
            .strip_prefix(env!("CARGO_MANIFEST_DIR"))
            .unwrap_or(path);
        tactic_work::write(
            "mdtests",
            &relative.display().to_string(),
            relative,
            &samples,
            |claim, source_index| {
                let position = match (&inputs, &project) {
                    (VerificationInput::Bundle(sources), Some(project)) => {
                        project_tactic_source_position(
                            project,
                            &ProgramInputs::Bundle(source_refs(sources)),
                            claim,
                            source_index,
                        )
                    }
                    (VerificationInput::Bundle(sources), None) => c_tactic_source_position(
                        click_source,
                        &source_refs(sources),
                        claim,
                        source_index,
                    ),
                    (VerificationInput::PreparedProgram(import), Some(project)) => {
                        project_tactic_source_position(
                            project,
                            &ProgramInputs::program(import),
                            claim,
                            source_index,
                        )
                    }
                    _ => return None,
                };
                position
                    .ok()
                    .map(|position| (position.line + line_offset, position.column))
            },
        );
    }
    if mdtest.quick_solve {
        quick_solve::check_quick_solve(&samples, &result)?;
    }
    check_expectation(path, expectation, result)
}

#[test]
fn quick_solve_caps_inclusive_work() {
    let samples = [instrumentation::TacticWorkSample {
        tactic: instrumentation::TacticEvent {
            source_tactic_path: None,
            claim: "transitive".into(),
            tactic_index: 0,
            tactic_name: "close".into(),
            class: "smart".into(),
            statement_index: 0,
            source_index: 0,
        },
        work: 2,
        inclusive_work: 10,
        failed: true,
    }];
    let mut samples = samples.to_vec();
    let mut termination = samples[0].clone();
    termination.tactic.claim = "program.termination".into();
    termination.inclusive_work = 100;
    samples.push(termination);
    let mut direct_close = samples[0].clone();
    direct_close.tactic.tactic_name = "close".into();
    direct_close.tactic.class = "simple".into();
    samples.push(direct_close);
    quick_solve::check_quick_solve_with_limit(&samples, &Ok(()), Some(10)).unwrap();
    let error = quick_solve::check_quick_solve_with_limit(&samples, &Ok(()), Some(9)).unwrap_err();
    assert!(error.contains("10 deterministic work units (limit 9)"));

    let direct_only = &samples[2..];
    quick_solve::check_quick_solve_with_limit(direct_only, &Ok(()), Some(10)).unwrap();
}

fn check_expectation(
    path: &Path,
    expectation: &MdTestExpectation,
    result: Result<(), ClickError>,
) -> Result<(), String> {
    let result = match result {
        Ok(()) => Ok(()),
        Err(error) if matches!(expectation, MdTestExpectation::Pass) => Err(error.report()),
        Err(error) => {
            let report = error.report();
            if let Some(internal) = ["SymbolicMemory {", "HeapMemory {", "pointer(pointer "]
                .into_iter()
                .find(|internal| report.contains(internal))
            {
                return Err(format!(
                    "`{}` leaked `{internal}` in its proof report: {report}",
                    path.display()
                ));
            }
            Err(click::surface::display_source_names(error.message()).into_owned())
        }
    };
    check_rendered_expectation(path, expectation, result)
}

fn check_rendered_expectation(
    path: &Path,
    expectation: &MdTestExpectation,
    result: Result<(), String>,
) -> Result<(), String> {
    match (expectation, result) {
        (MdTestExpectation::Pass, Ok(())) => Ok(()),
        (MdTestExpectation::Pass, Err(error)) => Err(format!(
            "`{}` expected pass, but failed: {error}",
            path.display()
        )),
        (MdTestExpectation::FailContains(expected), Ok(())) => Err(format!(
            "`{}` expected failure containing `{expected}`, but passed",
            path.display()
        )),
        (MdTestExpectation::FailContains(expected), Err(message)) => {
            if message.contains(expected) {
                Ok(())
            } else {
                Err(format!(
                    "`{}` expected failure containing `{expected}`, got `{message}`",
                    path.display()
                ))
            }
        }
    }
}

#[test]
fn sidecar_fixtures_propagate_verification_errors() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("proof.click");
    fs::write(
        &path,
        "theorem valid() { ensures 1 == 1 by { normalize(); } }",
    )
    .unwrap();
    run_mdtest(&path).expect("a checked sidecar proof passes");
    fs::write(
        &path,
        "theorem invalid() { ensures 1 == 2 by { normalize(); } }",
    )
    .unwrap();
    let error =
        run_mdtest(&path).expect_err("a successful input summary cannot hide a failed proof");
    assert!(error.contains("did not normalize to true"), "{error}");
    fs::write(&path, "theorem malformed(").unwrap();
    assert!(
        run_mdtest(&path).is_err(),
        "a failed input summary still fails"
    );
}
