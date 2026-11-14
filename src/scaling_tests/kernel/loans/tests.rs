// Scaling tests of `src/kernel/loans.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// One fixed view requirement, with independently varied irrelevant observations.
/// Measure both the planner's current selection expression and the real call.
/// Index preparation, resource insertion and loan construction are outside both.
#[test]
fn parent_loan_binding_selection_ignores_unbound_observations() {
    check_parent_binding_observation_scaling(&["early", "late", "two_bindings", "subrange"]);
}

#[test]
fn parent_loan_binding_refusals_and_owner_selection_ignore_observations() {
    check_parent_binding_observation_scaling(&["unbound", "owner", "stale"]);
}

fn check_parent_binding_observation_scaling(cases: &[&str]) {
    let mut curves = Vec::new();
    for &case in cases {
        let mut samples = Vec::new();
        for count in [4usize, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let facts = PureFactContext::new();
            let owned = memory(0, 8, true);
            let view = memory(0, 8, false);
            let (mut ledger, caller, callee) = participants();
            let support = backing(&owned);
            let opening = ledger.lend(caller, caller, support, owned.clone()).unwrap();
            if case != "owner" {
                ledger = ledger.apply(&opening.transition).unwrap();
            }
            let mut binding = LoanViewBinding {
                loan: opening.loan,
                scope: opening.scope,
                share: opening.root_share,
                support,
                viewed: view.clone(),
                hold: None,
            };
            let mut second_binding = None;
            if case == "two_bindings" {
                let (split, left, right) = ledger
                    .split(opening.root_share, caller, caller, caller)
                    .unwrap();
                ledger = ledger.apply(&split).unwrap();
                binding.share = left;
                second_binding = Some(LoanViewBinding {
                    share: right,
                    ..binding.clone()
                });
            }
            if case == "stale" {
                ledger = ledger
                    .apply(&ledger.end(opening.scope, caller).unwrap())
                    .unwrap();
                let (recovery, _, _) = ledger.recover(opening.loan, caller).unwrap();
                ledger = ledger.apply(&recovery).unwrap();
            }
            let (mut resources, occurrences) = ResourceContext::new_with_equalities(&facts)
                .unchecked_with_facts_and_occurrences(std::iter::repeat_n(view.clone(), count + 1));
            let first = occurrences[0].1;
            let last = occurrences[count].1;
            let mut bindings = LoanViewBindings::default();
            let expected = match case {
                "early" | "two_bindings" | "subrange" => Some(first),
                "late" | "stale" => Some(last),
                _ => None,
            };
            if let Some(occurrence) = expected {
                bindings = bindings.with_inserted(occurrence, binding);
            }
            if let Some(binding) = second_binding {
                bindings = bindings.with_inserted(last, binding);
            }
            if case == "owner" {
                resources = resources.unchecked_with_fact(owned);
            }
            resources = resources.with_loan_dependency_state(bindings.state());
            resources.synchronize_memory_equalities(&facts);
            let required = if case == "subrange" {
                memory(2, 4, false)
            } else {
                view.clone()
            };
            let requirements = [checked(required.clone())];
            let select = |bindings: &LoanViewBindings| {
                bindings.select_bound_view(&required, &resources, &facts)
            };
            let mut queries = Vec::new();
            for _ in 0..3 {
                let ((selected, work), map_work) =
                    crate::persistent::measure_persistent_work(|| {
                        crate::instrumentation::measure_deterministic_work(|| select(&bindings))
                    });
                assert_eq!(selected, expected, "{case}, {count}");
                let ((plan, call_work), call_maps) =
                    crate::persistent::measure_persistent_work(|| {
                        crate::instrumentation::measure_deterministic_work(|| {
                            plan_stable_view_transfer_with_bindings(
                                &resources,
                                &requirements,
                                &facts,
                                &ledger,
                                caller,
                                callee,
                                &bindings,
                            )
                        })
                    });
                if matches!(case, "unbound" | "stale") {
                    assert_eq!(
                        plan,
                        Err(StableViewPlanError::Loan(LoanRefusal::MissingLoanBinding)),
                        "{case}, {count}"
                    );
                } else {
                    assert!(plan.is_ok(), "{case}, {count}: {plan:?}");
                }
                queries.push((work, map_work, call_work, call_maps));
            }
            if case == "late" {
                let child = bindings.without(last);
                assert_eq!(select(&child), None);
                assert_eq!(select(&bindings), Some(last));
                assert!(
                    plan_stable_view_transfer_with_bindings(
                        &resources,
                        &requirements,
                        &facts,
                        &ledger,
                        caller,
                        callee,
                        &child,
                    )
                    .is_err(),
                    "removing the binding cannot promote an observation"
                );
            }
            samples.push((count, queries));
        }
        eprintln!(
            "parent binding {case} (count; selection work/maps, call work/maps): {samples:?}"
        );
        curves.push((case, samples));
    }
    for (case, samples) in &curves {
        assert!(
            samples[3]
                .1
                .iter()
                .zip(&samples[0].1)
                .all(|(large, small)| {
                    large.0 <= small.0 + 64
                        && large.1 <= small.1 * 3 + 256
                        && large.2 <= small.2 + 64
                        && large.3 <= small.3 + 512
                }),
            "parent binding selection scans observations ({case}): {samples:?}"
        );
    }
}

/// Binding updates, including replacements and removals, maintain persistent
/// indexes. Query cost depends on indexed depth, not the number of bindings.
#[test]
fn bound_view_selection_is_indexed_and_branch_local() {
    let mut costs = Vec::new();
    for count in [4u32, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let facts = PureFactContext::new();
        let view = memory(0, 8, false);
        let (ledger, caller, _) = participants();
        let owner = memory(0, 8, true);
        let opening = ledger.lend(caller, caller, backing(&owner), owner).unwrap();
        let template = LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support: opening.description.support(),
            viewed: view.clone(),
            hold: None,
        };
        let (mut resources, first) = ResourceContext::new_with_equalities(&facts)
            .unchecked_with_facts_and_occurrences([view.clone()]);
        let selected = first[0].1;
        let sole_live_view = resources.clone();
        let mut bindings = LoanViewBindings::default().with_inserted(selected, template.clone());
        for index in 0..count {
            let other = memory(16 + index * 8, 24 + index * 8, false);
            let (next, occurrences) =
                resources.unchecked_with_facts_and_occurrences([other.clone()]);
            resources = next;
            bindings = bindings.with_inserted(
                occurrences[0].1,
                LoanViewBinding {
                    viewed: other,
                    ..template.clone()
                },
            );
        }
        resources.synchronize_memory_equalities(&facts);
        let (found, work) = crate::persistent::measure_persistent_work(|| {
            bindings.select_bound_view(&view, &resources, &facts)
        });
        assert_eq!(found, Some(selected));
        // Retained metadata may outlive its resource occurrence, as at loop
        // entry. The live-view index selects the one covering occurrence;
        // there is no scan of the old metadata or of other live views.
        sole_live_view.synchronize_memory_equalities(&facts);
        let subrange = memory(2, 4, false);
        assert_eq!(bindings.bound_view_candidate(&subrange), None);
        let (live, live_work) = crate::persistent::measure_persistent_work(|| {
            bindings.select_bound_view(&subrange, &sole_live_view, &facts)
        });
        assert_eq!(live, Some(selected));
        assert_eq!(
            bindings.select_bound_view(&subrange, &resources, &facts),
            Some(selected)
        );
        costs.push((work, live_work));
        let removed = bindings.without(selected);
        assert_eq!(removed.bound_view_candidate(&view), None);
        assert_eq!(bindings.bound_view_candidate(&view), Some(selected));
        let replacement = memory(4000, 4008, false);
        let replaced = bindings.with_inserted(
            selected,
            LoanViewBinding {
                viewed: replacement.clone(),
                ..template
            },
        );
        assert_eq!(replaced.bound_view_candidate(&view), None);
        assert_eq!(replaced.bound_view_candidate(&replacement), Some(selected));
        // A nominated identity with the wrong held view is not authority.
        assert_eq!(
            replaced.select_bound_view(&replacement, &resources, &facts),
            None
        );
        assert_eq!(
            bindings.select_bound_view(&view, &resources, &facts),
            Some(selected)
        );
    }
    assert!(costs[3].0 <= costs[0].0 * 3 + 128, "{costs:?}");
    assert!(costs[3].1 <= costs[0].1 + 128, "{costs:?}");
}

#[test]
fn memory_split_origin_lookup_does_not_follow_successive_splits() {
    let mut samples = Vec::new();
    for count in [4u32, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let assumptions = PureFactContext::new();
        let owner = memory(0, count + 2, true);
        let mut resources =
            ResourceContext::new_with_equalities(&assumptions).unchecked_with_fact(owner.clone());
        let original = resources.occurrences_for_fact(&owner)[0];
        let mut origins = MemorySplitOrigins::default();
        for start in 0..count {
            let (next, _, next_origins) = resources
                .reserve_owned_memory_fragments_with_origins(
                    &memory(start, start + 1, true),
                    &assumptions,
                    &origins,
                )
                .unwrap();
            resources = next;
            origins = next_origins;
        }
        let (remaining, _) = resources
            .directly_supporting_owned_entry(&memory(count, count + 2, true), &assumptions)
            .unwrap();
        let mut queries = Vec::new();
        for _ in 0..3 {
            let ((source, work), map_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| origins.origin_of(remaining))
            });
            assert_eq!(source, original);
            queries.push((work, map_work));
        }
        samples.push(queries);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "origin lookup follows split history: {samples:?}"
    );
}

/// A fixed call consumes one half of an owner and borrows the other. Extra
/// observations of the borrowed slice are not alternative owned authority.
#[test]
fn split_owner_reconciliation_ignores_duplicate_observations() {
    let mut curves = Vec::new();
    for count in [4usize, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let assumptions = PureFactContext::new();
        let owner = memory(0, 8, true);
        let read = memory(6, 8, false);
        let selected = memory(6, 8, true);
        let resources = ResourceContext::new_with_equalities(&assumptions)
            .unchecked_with_fact(owner.clone())
            .unchecked_with_facts(std::iter::repeat_n(read.clone(), count));
        resources.synchronize_memory_equalities(&assumptions);
        let original = resources.occurrences_for_fact(&owner)[0];
        let mut consume = checked(memory(0, 4, true));
        consume.role = ResourceTransferRole::Consume;
        let requirements = [consume, checked(read)];
        let (ledger, caller, callee) = participants();
        let (residual, _, origins) = resources
            .clone()
            .reserve_owned_memory_fragments_with_origins(
                &requirements[0].fact,
                &assumptions,
                &MemorySplitOrigins::default(),
            )
            .expect("reserve the write and retain residual origins");
        let (remaining, _) = residual
            .directly_supporting_owned_entry(&selected, &assumptions)
            .expect("remaining read support");
        let mut helper_work = Vec::new();
        let mut helper_map_work = Vec::new();
        let mut call_map_work = Vec::new();
        let mut call_work = Vec::new();
        for _ in 0..3 {
            let ((other, units), map_units) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    origins.origin_of(remaining) == original
                })
            });
            assert!(other);
            helper_work.push(units);
            helper_map_work.push(map_units);
            let ((plan, units), map_units) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    plan_stable_view_transfer(
                        &resources,
                        &requirements,
                        &assumptions,
                        &ledger,
                        caller,
                        callee,
                    )
                })
            });
            let plan = plan.expect("disjoint write and view retain their original owner");
            assert_eq!(plan.stable_views().len(), 1);
            call_work.push(units);
            call_map_work.push(map_units);
        }
        // An independent equal-looking owner cannot acquire this origin.
        let child = resources.clone().unchecked_with_fact(selected.clone());
        let other = child.occurrences_for_fact(&selected)[0];
        assert_ne!(origins.origin_of(other), original);
        assert_eq!(origins.origin_of(remaining), original);
        curves.push((
            count,
            helper_work,
            call_work,
            helper_map_work,
            call_map_work,
        ));
    }
    eprintln!("split-owner reconciliation (count/helper/call/helper maps/call maps): {curves:?}");
    assert!(
        curves[3]
            .3
            .iter()
            .zip(&curves[0].3)
            .all(|(large, small)| *large <= *small * 3 + 128),
        "alternative-owner query traverses observations: {curves:?}"
    );
    assert!(
        curves.windows(2).all(|pair| pair[0]
            .1
            .iter()
            .zip(&pair[1].1)
            .all(|(small, large)| *large <= *small + 32)),
        "alternative-owner query scans observations: {curves:?}"
    );
    assert!(
        curves[3]
            .4
            .iter()
            .zip(&curves[0].4)
            .all(|(large, small)| *large <= *small + 1200),
        "complete call scans observations: {curves:?}"
    );
}

#[test]
fn concrete_view_carrier_recovery_ignores_unrelated_owners() {
    let mut samples = Vec::new();
    for size in [0u64, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let assumptions = PureFactContext::new();
        let (owner, requested) = opaque_memory_borrow_fixture();
        let requested = requested.fact.memory_own_range().unwrap();
        let views = [
            checked(ResourceFact::view_memory(requested.clone())),
            checked(ResourceFact::view_memory(
                crate::kernel::MemoryRange::new_with_element_width(
                    requested.base().clone(),
                    2u32.into(),
                    3u32.into(),
                    4,
                )
                .with_carrier_of(requested),
            )),
        ];
        let mut resources = ResourceContext::new().unchecked_with_fact(owner.clone());
        for extra in 0..size {
            resources = resources.unchecked_with_fact(ResourceFact::own_memory(
                crate::kernel::MemoryRange::new(
                    Pointer {
                        block: format!("unrelated-view-carrier-{extra}").into(),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    0u32.into(),
                    4u32.into(),
                ),
            ));
        }
        let (ledger, caller, callee) = participants();
        let (recovery, work) = crate::instrumentation::measure_deterministic_work(|| {
            plan_stable_view_transfer(&resources, &views, &assumptions, &ledger, caller, callee)?
                .recover_stable_views(&assumptions, &BTreeMap::new(), &[])
        });
        assert!(
            recovery
                .unwrap()
                .resources
                .satisfies_fact(&owner, &assumptions)
        );
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] * 4),
        "concrete-view recovery work grew with unrelated owners: {samples:?}"
    );
}

#[test]
fn partial_borrow_carrier_return_ignores_unrelated_owners() {
    let mut samples = Vec::new();
    for size in [0u64, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let assumptions = PureFactContext::new();
        let (owner, requested) = opaque_memory_borrow_fixture();
        let mut resources = ResourceContext::new().unchecked_with_fact(owner.clone());
        for extra in 0..size {
            let range = crate::kernel::MemoryRange::new(
                Pointer {
                    block: format!("unrelated-carrier-{extra}").into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                0u32.into(),
                4u32.into(),
            );
            resources = resources.unchecked_with_fact(ResourceFact::own_memory(range));
        }
        let (ledger, caller, callee) = participants();
        let (plan, work) = crate::instrumentation::measure_deterministic_work(|| {
            plan_stable_view_transfer(
                &resources,
                &[requested],
                &assumptions,
                &ledger,
                caller,
                callee,
            )
        });
        let plan = plan.unwrap();
        let returned = plan.canonical_transferred_ownership[0].as_ref().unwrap();
        assert_eq!(
            returned.memory_own_range().unwrap().access_designation(),
            owner.memory_own_range().unwrap().access_designation()
        );
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] * 4),
        "partial-borrow work grew with unrelated owners: {samples:?}"
    );
}

#[test]
fn mutex_contract_input_checks_ignore_unrelated_roots_at_multiple_sizes() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let (mut ledger, holder, input, description) = abstract_mutex_input();
        let fact = ledger.mutex_use_resource(input.usage, holder).unwrap();
        let mut resources = ResourceContext::new().unchecked_with_fact(fact);
        for index in 0..size {
            let (next, other) = ledger
                .borrowed_mutex_use_input(
                    holder,
                    backing(&owned("unrelated")),
                    Pointer::symbolic(Variable(1000 + index)),
                )
                .unwrap();
            ledger = next;
            resources = resources
                .unchecked_with_fact(ledger.mutex_use_resource(other.usage, holder).unwrap());
        }
        let (((), work), persistent) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let (child_state, child) = ledger
                    .reborrow_mutex_use(input.usage, holder, holder)
                    .unwrap();
                let (held, hold) = child_state
                    .hold_mutex_use(child.usage, &description, holder)
                    .unwrap();
                let released = held.release(hold, holder).unwrap();
                let (returned, _) = released
                    .end_mutex_reborrow_with_parent(&child, holder)
                    .unwrap();
                returned
                    .check_mutex_use_input_return(&input, holder, &resources)
                    .unwrap();
            })
        });
        samples.push((size, work, persistent));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 2 && pair[1].2 <= pair[0].2 * 2,
            "mutex input boundary scans unrelated roots: {samples:?}"
        );
    }
}

#[test]
fn mutex_use_deep_reborrows_scale_without_ancestry_walks() {
    let mut samples = Vec::new();
    for depth in [16, 32, 64, 128] {
        let (ledger, owner, _) = participants();
        let live = mutex_owner(Some(1));
        let (mut ledger, root) = ledger
            .lend_mutex_use(owner, owner, backing(&live), live.clone())
            .unwrap();
        let (((), work), persistent_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let mut parent = root.usage;
                let mut children = Vec::new();
                for _ in 0..depth {
                    let (next, child) = ledger.reborrow_mutex_use(parent, owner, owner).unwrap();
                    ledger = next;
                    let (held, hold) = ledger.hold_mutex_use(child.usage, &live, owner).unwrap();
                    ledger = held.release(hold, owner).unwrap();
                    parent = child.usage;
                    children.push(child);
                }
                for child in children.iter().rev() {
                    ledger = ledger.end_mutex_reborrow(child, owner).unwrap();
                }
            })
        });
        let (ledger, recovered) = ledger.recover_mutex_use(&root, owner).unwrap();
        assert_eq!(recovered, live);
        assert!(ledger.invariant_holds());
        samples.push((depth, work, persistent_work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 3 && pair[1].2 <= pair[0].2 * 3,
            "mutex reborrow work grows with ancestry: {samples:?}"
        );
    }
}

#[test]
fn lifetime_holds_scale_with_selected_shares() {
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let (mut ledger, owner, reader) = participants();
        let mut bindings = Vec::new();
        for i in 0..size {
            let fact = owned(&format!("lifetime-{i}"));
            let support = backing(&fact);
            let opening = ledger.lend(owner, reader, support, fact).unwrap();
            ledger = ledger.apply(&opening.transition).unwrap();
            bindings.push(LoanAuthorityBinding {
                loan: opening.loan,
                scope: opening.scope,
                share: opening.root_share,
                support,
            });
        }
        let (((), work), persistent_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for binding in bindings {
                    let (held, hold, _) = ledger
                        .hold_authority_with_transition(binding, reader)
                        .unwrap();
                    ledger = held.release(hold, reader).unwrap();
                }
            })
        });
        assert!(ledger.invariant_holds());
        samples.push((size, work, persistent_work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 3 && pair[1].2 <= pair[0].2 * 3,
            "lifetime holds scan unrelated loans: {samples:?}"
        );
    }
}

#[test]
fn completed_call_history_does_not_slow_outer_ledger_lookup() {
    let assumptions = PureFactContext::new();
    let owner = memory(0, 4, true);
    let caller_resources = ResourceContext::new().unchecked_with_fact(owner);
    let (ledger, caller, callee) = participants();
    let plan = plan_stable_view_transfer(
        &caller_resources,
        &[checked(memory(0, 2, false))],
        &assumptions,
        &ledger,
        caller,
        callee,
    )
    .unwrap();
    let recovery = plan
        .clone()
        .recover_stable_views(&assumptions, &BTreeMap::new(), &[])
        .unwrap();
    let evidence = Arc::new(CheckedLoanCallEvidence::new(
        plan,
        recovery.ledger,
        recovery.terminal_ledger,
        recovery.transitions,
        recovery.hold_base_ledger,
        recovery.hold_transitions,
    ));
    let mut samples = Vec::new();
    for size in [16_usize, 32, 64, 128] {
        let mut sequence = empty_checked_loan_evidence_sequence();
        for _ in 0..size {
            sequence = append_checked_loan_evidence(&sequence, Some(evidence.clone()));
        }
        let ((valid, recovered), work) = crate::persistent::measure_persistent_work(|| {
            (
                sequence.is_valid(),
                sequence.recovered_ledger_for(&ledger, caller, false),
            )
        });
        assert!(valid);
        assert_eq!(recovered, Some(ledger.clone()));
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(8),
            "outer ledger lookup grew with completed history: {samples:?}"
        );
    }
}

#[test]
fn deep_split_read_join_work_scales_with_explicit_tree_delta() {
    let mut samples = Vec::new();
    for depth in [16_usize, 32, 64, 128] {
        let (base, owner, _reader) = participants();
        let escrow = owned("deep-tree");
        let opening = base.lend(owner, owner, backing(&escrow), escrow).unwrap();
        let mut ledger = base.apply(&opening.transition).unwrap();
        let (((), work), persistent_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let mut current = opening.root_share;
                let mut parents = Vec::with_capacity(depth);
                let mut siblings = Vec::with_capacity(depth);
                for _ in 0..depth {
                    let (split, left, right) = ledger.split(current, owner, owner, owner).unwrap();
                    ledger = ledger.apply(&split).unwrap();
                    parents.push(current);
                    siblings.push(right);
                    current = left;
                }
                assert!(ledger.permits_view(
                    owner,
                    &opening.description,
                    current,
                    &PureFactContext::new()
                ));
                for (parent, sibling) in parents.into_iter().zip(siblings).rev() {
                    let join = ledger.join(current, sibling, owner).unwrap();
                    ledger = ledger.apply(&join).unwrap();
                    current = parent;
                }
                assert_eq!(current, opening.root_share);
                assert!(ledger.invariant_holds());
            })
        });
        samples.push((depth, work, persistent_work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3) && pair[1].2 <= pair[0].2.saturating_mul(3),
            "deep split/read/join work exceeded the explicit tree delta: {samples:?}"
        );
    }
}

#[test]
fn dependency_updates_scale_with_changed_scope_entries() {
    let mut samples = Vec::new();
    for size in [16_usize, 32, 64, 128] {
        let (mut ledger, owner, _reader) = participants();
        let parent_fact = owned("dependency-parent");
        let parent = ledger
            .lend(owner, owner, backing(&parent_fact), parent_fact)
            .unwrap();
        ledger = ledger.apply(&parent.transition).unwrap();
        let mut children = Vec::with_capacity(size);
        for index in 0..size {
            let child_fact = owned(&format!("dependency-child-{index}"));
            let child = ledger
                .lend(owner, owner, backing(&child_fact), child_fact)
                .unwrap();
            ledger = ledger.apply(&child.transition).unwrap();
            children.push(child);
        }
        let (((), work), persistent_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for child in &children {
                    let transition = ledger
                        .register_dependency(parent.scope, child.scope, owner)
                        .unwrap();
                    ledger = ledger.apply(&transition).unwrap();
                }
            })
        });
        samples.push((size, work, persistent_work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3) && pair[1].2 <= pair[0].2.saturating_mul(3),
            "dependency updates visited unrelated scope entries: {samples:?}"
        );
    }
}

#[test]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn disjoint_memory_view_clustering_has_linear_overlap_work() {
    let assumptions = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [16_usize, 32, 64, 128] {
        let ledger = LoanLedger::new();
        let caller = ledger.fresh_participant().unwrap();
        let callee = ledger.fresh_participant().unwrap();
        let caller_resources =
            ResourceContext::new().unchecked_with_fact(memory(0, (size * 2 + 1) as u32, true));
        let requirements = (0..size)
            .map(|index| checked(memory((index * 2) as u32, (index * 2 + 1) as u32, false)))
            .collect::<Vec<_>>();
        let (plan, work) = crate::instrumentation::measure_deterministic_work(|| {
            plan_stable_view_transfer(
                &caller_resources,
                &requirements,
                &assumptions,
                &ledger,
                caller,
                callee,
            )
        });
        let plan = plan.expect("disjoint concrete views should form independent loans");
        assert_eq!(plan.stable_views().len(), size);
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "disjoint view clustering compared unrelated candidates: {samples:?}"
        );
    }
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn overlapping_memory_view_clustering_handles_chains_and_equal_starts() {
    let assumptions = PureFactContext::new();
    let mut chain_samples = Vec::new();
    let mut equal_start_samples = Vec::new();
    for size in [4_usize, 8, 16, 32] {
        let ledger = LoanLedger::new();
        let caller = ledger.fresh_participant().unwrap();
        let callee = ledger.fresh_participant().unwrap();
        let mut caller_resources = ResourceContext::new();
        let mut chain_requirements = Vec::with_capacity(size * 3);
        let mut equal_requirements = Vec::with_capacity(size * 3);
        for index in 0..size {
            let base = crate::kernel::Pointer {
                block: crate::kernel::PointerBlock::Concrete(format!("overlap-{index}")),
                offset: crate::kernel::PointerOffsetTerm::Constant(0),
            };
            let owner = ResourceFact::own_memory(MemoryRange::new(
                base.clone(),
                MachineTerm::constant(0),
                MachineTerm::constant(6),
            ));
            caller_resources = caller_resources.unchecked_with_fact(owner);
            let view = |start, end| {
                checked(ResourceFact::view_memory(MemoryRange::new(
                    base.clone(),
                    MachineTerm::constant(start),
                    MachineTerm::constant(end),
                )))
            };
            // Three clauses form a transitive overlap chain. Keeping the
            // chain bounded avoids making resource validity itself the
            // measured axis while the number of independent chains grows.
            chain_requirements.extend([view(0, 3), view(2, 5), view(4, 6)]);
            equal_requirements.extend([view(0, 2), view(0, 2), view(0, 2)]);
        }
        let (chain, chain_work) = crate::instrumentation::measure_deterministic_work(|| {
            plan_stable_view_transfer(
                &caller_resources,
                &chain_requirements,
                &assumptions,
                &ledger,
                caller,
                callee,
            )
        });
        let chain = chain.expect("overlapping chains should share backing loans");
        assert_eq!(chain.stable_views().len(), size * 3);
        chain_samples.push((size, chain_work));

        let (equal_start, equal_start_work) =
            crate::instrumentation::measure_deterministic_work(|| {
                plan_stable_view_transfer(
                    &caller_resources,
                    &equal_requirements,
                    &assumptions,
                    &ledger,
                    caller,
                    callee,
                )
            });
        let equal_start = equal_start.expect("equal-start views should share backing loans");
        assert_eq!(equal_start.stable_views().len(), size * 3);
        equal_start_samples.push((size, equal_start_work));
    }
    for samples in [&chain_samples, &equal_start_samples] {
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 <= pair[0].1.saturating_mul(3),
                "overlap clustering work exceeded its explicit view delta: {samples:?}"
            );
        }
    }
    {
        let costs = chain_samples
            .iter()
            .map(|(_, work)| *work)
            .collect::<Vec<_>>();
        let linear = |costs: &[usize]| {
            costs.windows(3).all(|triple| {
                let first = triple[1] - triple[0];
                let second = triple[2] - triple[1];
                second <= first * 2 + 128
            })
        };
        assert!(linear(&costs), "transition work: {costs:?}");
        let rescanned = chain_samples
            .iter()
            .map(|(size, work)| work + size * size)
            .collect::<Vec<_>>();
        assert!(
            !linear(&rescanned),
            "the smaller fixture must detect quadratic transition work: {costs:?}"
        );
    }
    {
        let costs = equal_start_samples
            .iter()
            .map(|(_, work)| *work)
            .collect::<Vec<_>>();
        let linear = |costs: &[usize]| {
            costs.windows(3).all(|triple| {
                let first = triple[1] - triple[0];
                let second = triple[2] - triple[1];
                second <= first * 2 + 128
            })
        };
        assert!(linear(&costs), "transition work: {costs:?}");
        let rescanned = equal_start_samples
            .iter()
            .map(|(size, work)| work + size * size)
            .collect::<Vec<_>>();
        assert!(
            !linear(&rescanned),
            "the smaller fixture must detect quadratic transition work: {costs:?}"
        );
    }
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn loan_certificate_recheck_scales_with_explicit_transition_delta() {
    let assumptions = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [4_usize, 8, 16, 32] {
        let ledger = LoanLedger::new();
        let caller = ledger.fresh_participant().unwrap();
        let callee = ledger.fresh_participant().unwrap();
        let caller_resources =
            ResourceContext::new().unchecked_with_fact(memory(0, (size * 2 + 1) as u32, true));
        let requirements = (0..size)
            .map(|index| checked(memory((index * 2) as u32, (index * 2 + 1) as u32, false)))
            .collect::<Vec<_>>();
        let plan = plan_stable_view_transfer(
            &caller_resources,
            &requirements,
            &assumptions,
            &ledger,
            caller,
            callee,
        )
        .unwrap();
        let planned_ledger = plan.ledger.clone();
        let recovery = plan
            .clone()
            .recover_stable_views(&assumptions, &BTreeMap::new(), &[])
            .unwrap();
        let evidence = CheckedLoanCallEvidence::new(
            plan,
            recovery.ledger,
            recovery.terminal_ledger,
            recovery.transitions,
            recovery.hold_base_ledger,
            recovery.hold_transitions,
        );
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            evidence
                .recheck(&ledger, Some(caller), &planned_ledger, Some(callee))
                .unwrap();
        });
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "certificate recheck work exceeded its explicit transition delta: {samples:?}"
        );
    }
    {
        let costs = samples.iter().map(|(_, work)| *work).collect::<Vec<_>>();
        let linear = |costs: &[usize]| {
            costs.windows(3).all(|triple| {
                let first = triple[1] - triple[0];
                let second = triple[2] - triple[1];
                second <= first * 2 + 128
            })
        };
        assert!(linear(&costs), "transition work: {costs:?}");
        let rescanned = samples
            .iter()
            .map(|(size, work)| work + size * size)
            .collect::<Vec<_>>();
        assert!(
            !linear(&rescanned),
            "the smaller fixture must detect quadratic transition work: {costs:?}"
        );
    }
}

#[test]
fn offset_alias_overlap_uses_exact_bytes_and_ignores_unrelated_facts() {
    use crate::kernel::{ConditionTerm, Pointer, PointerOffsetTerm};
    let p = Pointer {
        block: "overlap".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let q = Pointer {
        block: p.block.clone(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(600)), 1),
    };
    let protected = MemoryRange::new_with_element_width(
        p.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(1),
        4,
    );
    let mut samples = Vec::new();
    let sizes = [4u64, 16, 64, 256];
    for size in sizes {
        let mut assumptions = PureFactContext::new();
        for index in 0..size {
            assumptions = assumptions.assume_condition(
                ConditionTerm::equal(
                    MachineTerm::Variable(Variable(1000 + index)),
                    MachineTerm::constant(0),
                ),
                true,
            );
        }
        for (offset, width, overlaps) in [
            (3, 1, true),
            (4, 1, false),
            (-1, 2, true),
            (4_294_967_297, 8, false),
        ] {
            let equality = ConditionTerm::pointer_offset_equal(
                q.offset.clone(),
                PointerOffsetTerm::Constant(offset),
            );
            let context = assumptions.clone().assume_condition(equality.clone(), true);
            let query = MemoryRange::new_with_element_width(
                q.clone(),
                MachineTerm::constant(0),
                MachineTerm::constant(1),
                width,
            );
            let (actual, work) = crate::instrumentation::measure_deterministic_work(|| {
                protected_range_proven_overlapping(&query, &protected, &context)
            });
            assert_eq!(actual, overlaps);
            if offset == 3 {
                samples.push(work);
            }
            assert!(
                assumptions
                    .exact_pointer_offset_aliases(&q)
                    .next()
                    .is_none()
            );
        }
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] * 2 + 16),
        "overlap query scanned unrelated facts: {samples:?}"
    );
    let indexed = |costs: &[usize]| costs.iter().all(|work| *work <= costs[0] + 32);
    assert!(indexed(&samples), "{samples:?}");
    let rescanned = samples
        .iter()
        .zip(sizes)
        .map(|(work, size)| work + usize::try_from(size).unwrap())
        .collect::<Vec<_>>();
    assert!(
        !indexed(&rescanned),
        "the smaller overlap fixture must detect unrelated fact visits: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn joint_fragment_reservation_does_not_scan_ambient_memory_with_scalar_equalities() {
    let facts = PureFactContext::new().assume_condition(
        ConditionTerm::equal(
            MachineTerm::Variable(Variable(944_023)),
            MachineTerm::constant(7),
        ),
        true,
    );
    assert!(facts.equality_graph.has_term_equivalences());
    let (ledger, caller, callee) = participants();
    let required = checked(memory(0, 4, true));
    let mut samples = Vec::new();
    for count in [16, 64, 256, 1024] {
        let mut resources = ResourceContext::new()
            .unchecked_with_fact(memory(0, 2, true))
            .unchecked_with_fact(memory(2, 3, true))
            .unchecked_with_fact(memory(3, 4, true));
        for index in 0..count {
            resources =
                resources.unchecked_with_fact(memory(8192 + index * 2, 8193 + index * 2, true));
        }
        resources.synchronize_memory_equalities(&facts);
        let ((plan, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                plan_stable_view_transfer(
                    &resources,
                    std::slice::from_ref(&required),
                    &facts,
                    &ledger,
                    caller,
                    callee,
                )
                .unwrap()
            })
        });
        assert_eq!(plan.reserved_ownership_supports.len(), 3);
        samples.push((work, map_work));
    }
    assert!(
        samples[3].0 <= samples[0].0 * 2 + 64,
        "ambient ownership scan: {samples:?}"
    );
    assert!(
        samples[3].1 <= samples[0].1 * 4 + 256,
        "ambient index scan: {samples:?}"
    );
}

#[test]
fn active_memory_witness_ignores_unrelated_live_loans() {
    let mut samples = Vec::new();
    for size in [16_usize, 32, 64, 128] {
        let (mut ledger, owner, reader) = participants();
        for index in 0..size {
            let owned_range = memory((index * 2) as u32, (index * 2 + 1) as u32, true);
            let opening = ledger
                .lend(owner, reader, backing(&owned_range), owned_range)
                .unwrap();
            ledger = ledger.apply(&opening.transition).unwrap();
        }
        let query = memory(0, 1, false).memory_range().unwrap().clone();
        let (loan, work) = crate::instrumentation::measure_deterministic_work(|| {
            ledger.first_active_memory_overlap(&query).unwrap()
        });
        assert!(loan.is_some());
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(8),
            "active interval candidates scanned unrelated live loans: {samples:?}"
        );
    }
}

/// A view no single owner covers, over owned pieces of different element
/// widths that tile it, is explicitly composed before it is lent. The
/// composition reads only the pieces under the view, never the unrelated owners
/// beside them.
#[test]
fn mixed_width_view_backing_joins_only_its_own_pieces() {
    let (ledger, caller, callee) = participants();
    let piece = |start: u32, end: u32, width: u32| {
        ResourceFact::own_memory(crate::kernel::MemoryRange::new_with_element_width(
            crate::kernel::Pointer {
                block: "buffer".into(),
                offset: crate::kernel::PointerOffsetTerm::Constant(0),
            },
            crate::kernel::MachineTerm::constant(start),
            crate::kernel::MachineTerm::constant(end),
            width,
        ))
    };
    let required = checked(memory(0, 4, false));
    let facts = PureFactContext::new();
    let mut samples = Vec::new();
    for count in [16, 64, 256, 1024] {
        // Bytes 0..8 as bytes, then bytes 8..16 as two int32 cells.
        let mut resources = ResourceContext::new()
            .unchecked_with_fact(piece(0, 8, 1))
            .unchecked_with_fact(piece(2, 4, 4));
        for index in 0..count {
            resources =
                resources.unchecked_with_fact(memory(8192 + index * 2, 8193 + index * 2, true));
        }
        resources.synchronize_memory_equalities(&facts);
        let ((plan, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                // Explicit owned composition, as a fold/unfold before the call.
                let owner = memory(0, 4, true);
                let composed = resources
                    .clone()
                    .without_fact_incrementally(&owner, &facts)
                    .unwrap()
                    .try_compose_into_valid_context_delaying_normalization([owner], &facts)
                    .unwrap();
                plan_stable_view_transfer(
                    &composed,
                    std::slice::from_ref(&required),
                    &facts,
                    &ledger,
                    caller,
                    callee,
                )
                .unwrap()
            })
        });
        assert_eq!(plan.stable_views().len(), 1);
        samples.push((work, map_work));
    }
    assert!(
        samples[3].0 <= samples[0].0 * 2 + 64,
        "ambient ownership scan: {samples:?}"
    );
    assert!(
        samples[3].1 <= samples[0].1 * 4 + 256,
        "ambient index scan: {samples:?}"
    );
}

/// The call needs a fixed range. A gap immediately after its first four-byte cell cannot
/// be filled by any of the growing, disjoint fragments farther into the range.
#[test]
fn call_fragment_composition_stops_at_a_fixed_gap() {
    let mut curves = Vec::new();
    for case in ["gap", "joined", "owner", "observations"] {
        let mut samples = Vec::new();
        for count in [4u32, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let facts = PureFactContext::new();
            let required = memory(0, 1024, false);
            let mut resources =
                ResourceContext::new_with_equalities(&facts).unchecked_with_fact(memory(
                    0,
                    if case == "owner" {
                        1024
                    } else if case == "joined" {
                        512
                    } else {
                        1
                    },
                    true,
                ));
            if case == "joined" {
                resources = resources.unchecked_with_fact(memory(512, 1024, true));
            }
            for index in 0..count {
                let start = if matches!(case, "joined" | "owner") {
                    2048
                } else {
                    100
                } + 2 * index;
                resources =
                    resources.unchecked_with_fact(memory(start, start + 1, case != "observations"));
            }
            resources.synchronize_memory_equalities(&facts);
            let (ledger, caller, callee) = participants();
            let requirements = [checked(required.clone())];
            let bindings = LoanViewBindings::default();
            let original_len = resources.facts().len();
            let mut queries = Vec::new();
            for _ in 0..3 {
                let ((consumed, consume_work), consume_maps) =
                    crate::persistent::measure_persistent_work(|| {
                        crate::instrumentation::measure_deterministic_work(|| {
                            resources
                                .clone()
                                .without_fact_incrementally(&memory(0, 1024, true), &facts)
                        })
                    });
                assert_eq!(
                    consumed.is_some(),
                    matches!(case, "owner" | "joined"),
                    "{case}/{count}"
                );
                let ((plan, call_work), call_maps) =
                    crate::persistent::measure_persistent_work(|| {
                        crate::instrumentation::measure_deterministic_work(|| {
                            plan_stable_view_transfer_with_bindings(
                                &resources,
                                &requirements,
                                &facts,
                                &ledger,
                                caller,
                                callee,
                                &bindings,
                            )
                        })
                    });
                assert_eq!(plan.is_ok(), case == "owner", "{case}/{count}: {plan:?}");
                if let Ok(plan) = plan {
                    assert!(plan.callee_resources.satisfies_fact(&required, &facts));
                }
                assert_eq!(resources.facts().len(), original_len);
                assert!(resources.contains_exact_representation(&memory(
                    0,
                    if case == "owner" {
                        1024
                    } else if case == "joined" {
                        512
                    } else {
                        1
                    },
                    true
                )));
                queries.push((call_work, call_maps, consume_work, consume_maps));
            }
            samples.push((count, queries));
        }
        eprintln!("fragment {case} (count; call work/maps, consumption work/maps): {samples:?}");
        curves.push((case, samples));
    }
    // Check semantics for every size and control before checking the cost curves.
    for (case, samples) in &curves {
        assert!(
            samples[3]
                .1
                .iter()
                .zip(&samples[0].1)
                .all(|(large, small)| {
                    large.0 <= small.0 + 64
                        && large.1 <= small.1 * 3 + 256
                        && large.2 <= small.2 + 64
                        && large.3 <= small.3 * 3 + 256
                }),
            "fragment composition walks rejected candidates ({case}): {samples:?}"
        );
    }
}

#[test]
fn cache_protection_does_not_enumerate_overlapping_loans() {
    let mut samples = Vec::new();
    for count in [4, 16, 64] {
        let (mut ledger, holder, _) = participants();
        let view = memory(0, 8, false);
        let resources = ResourceContext::new().unchecked_with_fact(view.clone());
        let support = resources.occurrences_for_fact(&view)[0];
        for _ in 0..count {
            let opening = ledger
                .borrowed_contract_input(holder, support, view.clone(), None)
                .unwrap();
            ledger = ledger.apply(&opening.transition).unwrap();
        }
        let (protected, work) = crate::instrumentation::measure_deterministic_work(|| {
            ledger.has_indexed_memory_overlap(memory(2, 4, false).memory_range().unwrap())
        });
        assert!(protected);
        samples.push((count, work));
    }
    assert!(
        samples.iter().all(|(_, work)| *work == samples[0].1),
        "cache protection enumerated a loan bucket: {samples:?}"
    );
}

#[test]
fn write_barrier_does_not_enumerate_overlapping_loans() {
    for (name, start, end, blocked) in [
        ("inside", 2, 4, true),
        ("covering", 0, 16, true),
        ("adjacent", 8, 10, false),
    ] {
        let mut samples = Vec::new();
        let mut diagnostic_samples = Vec::new();
        for count in [4, 16, 64, 256] {
            let (mut ledger, holder, _) = participants();
            let view = memory(0, 8, false);
            let resources = ResourceContext::new().unchecked_with_fact(view.clone());
            let support = resources.occurrences_for_fact(&view)[0];
            let mut first = None;
            for _ in 0..count {
                let opening = ledger
                    .borrowed_contract_input(holder, support, view.clone(), None)
                    .unwrap();
                first.get_or_insert(opening.loan);
                ledger = ledger.apply(&opening.transition).unwrap();
            }
            let query = memory(start, end, false);
            let assumptions = PureFactContext::new();
            for repeat in 0..3 {
                let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                    ledger.permits_memory_access_with_assumptions(
                        query.memory_range().unwrap(),
                        &assumptions,
                    )
                });
                assert_eq!(
                    result,
                    if blocked {
                        Err(LoanRefusal::ActiveDependency)
                    } else {
                        Ok(())
                    }
                );
                samples.push((count, repeat, work));
                let (diagnostic, diagnostic_work) =
                    crate::instrumentation::measure_deterministic_work(|| {
                        ledger.memory_access_refusal(
                            query.memory_range().unwrap(),
                            &assumptions,
                            LoanRefusalOperation::MemoryAccess,
                        )
                    });
                assert_eq!(
                    diagnostic.as_ref().map(|d| d.category()),
                    blocked.then_some(LoanRefusalCategory::ActiveDependency)
                );
                assert_eq!(
                    diagnostic.map(|d| d.subject().loan_id()),
                    blocked.then(|| first.map(|loan| (loan.arena, loan.ordinal)))
                );
                diagnostic_samples.push((count, repeat, diagnostic_work));
            }
        }
        eprintln!("{name}: checking {samples:?}; diagnostics {diagnostic_samples:?}");
        assert!(
            diagnostic_samples
                .iter()
                .all(|(_, _, work)| *work <= diagnostic_samples[0].2 + 4),
            "{name}: diagnosing one write must not enumerate matches: {diagnostic_samples:?}"
        );
        assert!(samples[0].2 > 0, "{name}: no work measured");
        assert!(
            samples.iter().all(|(_, _, work)| *work <= samples[0].2 + 4),
            "{name}: one write must not enumerate all matching loans: {samples:?}"
        );
    }
}

#[test]
fn writes_without_active_memory_loans_do_not_walk_pointer_aliases() {
    for mode in ["empty", "token", "ended_memory"] {
        let (mut ledger, owner, reader) = participants();
        if mode != "empty" {
            let fact = if mode == "token" {
                owned("token")
            } else {
                memory(0, 8, true)
            };
            let opening = lend_test(&ledger, owner, reader, fact);
            ledger = ledger.apply(&opening.transition).unwrap();
            if mode == "ended_memory" {
                let returned = ledger.transfer(opening.root_share, reader, owner).unwrap();
                ledger = ledger.apply(&returned).unwrap();
                let ended = ledger.end(opening.scope, owner).unwrap();
                ledger = ledger.apply(&ended).unwrap();
            }
        }
        assert!(!ledger.has_active_memory_loans());
        assert!(ledger.invariant_holds());
        for symbolic_bound in [false, true] {
            let mut samples = Vec::new();
            for count in [4, 16, 64, 256] {
                let base = Pointer::symbolic(Variable(980_000));
                let mut facts = PureFactContext::new();
                for index in 0..count {
                    facts = facts.assume_condition(
                        ConditionTerm::pointer_equal(
                            base.clone(),
                            Pointer::symbolic(Variable(980_001 + index as u64)),
                        ),
                        true,
                    );
                }
                let end = if symbolic_bound {
                    MachineTerm::Variable(Variable(981_000))
                } else {
                    MachineTerm::constant(1)
                };
                let range = MemoryRange::new_with_element_width(base, 0u32.into(), end, 4);
                for repeat in 0..3 {
                    let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                        ledger.permits_memory_access_with_assumptions(&range, &facts)
                    });
                    assert_eq!(result, Ok(()));
                    let (report, diagnostic_work) =
                        crate::instrumentation::measure_deterministic_work(|| {
                            ledger.memory_access_refusal(
                                &range,
                                &facts,
                                LoanRefusalOperation::MemoryAccess,
                            )
                        });
                    assert!(report.is_none());
                    samples.push((count, repeat, work, diagnostic_work));
                }
            }
            eprintln!("{mode}, symbolic bounds {symbolic_bound}: {samples:?}");
            assert!(
                samples
                    .iter()
                    .all(|(_, _, work, diagnostic_work)| *work == 0 && *diagnostic_work == 0),
                "{mode}, symbolic bounds {symbolic_bound}: no memory loans must mean no alias candidates: {samples:?}"
            );
        }
    }
}

#[test]
fn loan_access_requirement_is_retained_and_branch_local() {
    let mut samples = Vec::new();
    for count in [4, 16, 64, 256] {
        let (mut ledger, holder, _) = participants();
        let owned = memory(0, 8, true);
        let query = memory(16, 20, false);
        let query = query.memory_range().unwrap();
        let empty = ledger.clone();
        let mut last = None;
        for _ in 0..count {
            let opening = lend_test(&ledger, holder, holder, owned.clone());
            ledger = ledger.apply(&opening.transition).unwrap();
            last = Some(opening);
        }
        let (requirement, work) = crate::instrumentation::measure_deterministic_work(|| {
            ledger.memory_access_requirement(query).unwrap()
        });
        let last = last.unwrap();
        let (child, close_work) = crate::instrumentation::measure_deterministic_work(|| {
            ledger
                .apply(&ledger.end(last.scope, holder).unwrap())
                .unwrap()
        });
        assert_ne!(
            child.memory_access_requirement(query),
            Some(requirement.clone())
        );
        assert_eq!(ledger.memory_access_requirement(query), Some(requirement));
        assert_eq!(empty.memory_access_requirement(query), None);
        samples.push((count, work, close_work));
    }
    eprintln!("retained loan requirements (loans, construction, close): {samples:?}");
    for sample in &samples {
        assert_eq!(sample.1, samples[0].1);
        assert!(sample.2 <= samples[0].2 + 32);
    }
}
