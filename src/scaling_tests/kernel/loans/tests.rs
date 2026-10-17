// Scaling tests of `src/kernel/loans.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

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
    for size in [16_usize, 32, 64, 128] {
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
            let owner = CResourceFact::own_memory(CMemoryRange::new(
                base.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(6),
            ));
            caller_resources = caller_resources.unchecked_with_fact(owner);
            let view = |start, end| {
                checked(CResourceFact::view_memory(CMemoryRange::new(
                    base.clone(),
                    Bitvector32Term::Constant(start),
                    Bitvector32Term::Constant(end),
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
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn loan_certificate_recheck_scales_with_explicit_transition_delta() {
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
}

#[test]
fn offset_alias_overlap_uses_exact_bytes_and_ignores_unrelated_facts() {
    use crate::kernel::{ConditionTerm, Pointer, PointerOffsetTerm, Proposition};
    let p = Pointer {
        block: "overlap".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let q = Pointer {
        block: p.block.clone(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(600)), 1),
    };
    let protected = CMemoryRange::new_with_element_width(
        p.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
        4,
    );
    let mut samples = Vec::new();
    for size in [8, 32, 128, 512] {
        let mut assumptions = PureFactContext::new();
        for index in 0..size {
            assumptions = assumptions.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(1000 + index)),
                    Bitvector32Term::Constant(0),
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
            let query = CMemoryRange::new_with_element_width(
                q.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
                width,
            );
            let (actual, work) = crate::instrumentation::measure_deterministic_work(|| {
                protected_range_proven_overlapping(&query, &protected, &context)
            });
            assert_eq!(actual, overlaps);
            if offset == 3 {
                samples.push(work);
            }
            let withdrawn = context.without_exact_fact(&Proposition::ConditionIs(equality, true));
            assert!(withdrawn.exact_pointer_offset_aliases(&q).next().is_none());
        }
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] * 2 + 16),
        "overlap query scanned unrelated facts: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn joint_fragment_reservation_does_not_scan_ambient_memory_with_scalar_equalities() {
    let facts = PureFactContext::new().assume_condition(
        ConditionTerm::equal(
            Bitvector32Term::Variable(Variable(944_023)),
            Bitvector32Term::Constant(7),
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
fn active_memory_candidates_ignore_unrelated_live_loans() {
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
        let (loans, work) = crate::instrumentation::measure_deterministic_work(|| {
            ledger.active_memory_overlaps(&query).unwrap()
        });
        assert_eq!(loans.len(), 1);
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
/// widths that tile it, is lent from the pieces joined into one owner. The
/// join reads only the pieces under the view, never the unrelated owners
/// beside them.
#[test]
fn mixed_width_view_backing_joins_only_its_own_pieces() {
    let (ledger, caller, callee) = participants();
    let piece = |start: u32, end: u32, width: u32| {
        CResourceFact::own_memory(crate::kernel::CMemoryRange::new_with_element_width(
            crate::kernel::Pointer {
                block: "buffer".into(),
                offset: crate::kernel::PointerOffsetTerm::Constant(0),
            },
            crate::kernel::Bitvector32Term::Constant(start),
            crate::kernel::Bitvector32Term::Constant(end),
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
