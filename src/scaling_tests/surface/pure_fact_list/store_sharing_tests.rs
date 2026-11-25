fn fact(index: u64, related: bool) -> Proposition {
    Proposition::Predicate {
        name: if related {
            "same_predicate".to_string()
        } else {
            format!("fact_{index}")
        },
        arguments: vec![crate::kernel::Term::Bitvector32(
            crate::kernel::OldMachineTerm::constant(index as u32).into(),
        )],
    }
}

/// Repeated proof/statement views share the ambient indexes and context.
/// Grow ambient facts and fork count together: rebuilding either representation
/// would index/copy n squared facts rather than the n explicit additions.
#[test]
fn statement_store_views_only_index_their_delta() {
    for related in [false, true] {
        let mut samples = Vec::new();
        for size in [32, 128, 512] {
            let root = PureFactStore::from_ordered(
                &(0..size)
                    .map(|index| fact(index, related))
                    .collect::<Vec<_>>(),
            );
            let before_lists = fact_list_entry_counts();
            let _ = crate::kernel::proof::take_fact_entry_counts();
            let before_contexts = crate::kernel::reasoning::path_facts::context_rebuild_entries();
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                for index in 0..size {
                    let mut view = PureFactList::from_produced_store(root.clone());
                    assert!(view.contains(&fact(index, related)));
                    view.push(fact(size + index, related));
                    let child = view.fact_store();
                    assert!(child.contains(&fact(size + index, related)));
                    assert!(!root.contains(&fact(size + index, related)));
                }
            });
            samples.push(work);
            let after_lists = fact_list_entry_counts();
            assert_eq!(
                after_lists, before_lists,
                "size {size}: no Surface copies/indexing"
            );
            let (indexed, materialized) = crate::kernel::proof::take_fact_entry_counts();
            assert_eq!(
                indexed, size as usize,
                "size {size}: only new facts indexed"
            );
            assert_eq!(materialized, 0, "size {size}: no ambient materialization");
            assert_eq!(
                crate::kernel::reasoning::path_facts::context_rebuild_entries(),
                before_contexts
            );
        }
        assert!(
            samples.windows(2).all(|pair| pair[1] <= pair[0] * 6 + 1024),
            "{samples:?}"
        );
    }
}

/// A restricted scope keeps the enclosing store's name reservations
/// without walking a retained fact's memory again.
#[test]
fn restricted_facts_keep_ambient_memory_reservations() {
    use crate::kernel::{
        Address, AddressBase, AddressOffset, OldMachineTerm, ProgramValue, SymbolicMemory, Variable,
    };
    for size in [32, 128, 512] {
        let pointer = |index| Address {
            base: AddressBase::ExternalObject(Variable(9_100_000 + index)),
            offset: AddressOffset::Constant(0),
        };
        let memory = (0..size).fold(SymbolicMemory::new(), |memory, index| {
            memory.store(
                pointer(index),
                ProgramValue::Int32(OldMachineTerm::Variable(Variable(9_200_000 + index))),
            )
        });
        crate::kernel::intern_memory(memory.clone());
        let selected = Proposition::MemoryLoadable {
            memory,
            base: pointer(0),
            bytes: (OldMachineTerm::constant(4)).into(),
            wide: false,
        };
        let discarded = fact(0, false);
        let ambient = PureFactStore::from_ordered(&[selected.clone(), discarded.clone()]);
        let before = crate::kernel::proof::reserved_fact_variable_entries();
        let local = ambient.retaining(|fact| fact == &selected);
        let collected = crate::kernel::proof::reserved_fact_variable_entries() - before;
        assert!(
            collected <= 4,
            "size {size}: recollected {collected} variables from ambient memory"
        );
        assert!(local.reserves_variable(Variable(9_200_000 + size - 1)));
        assert!(!local.contains_top_level(&discarded));
        assert!(local.contains_top_level(&selected));
    }
}

/// General views, prioritized statement publication, and cached-source adapters
/// must share the root just as the ordinary statement-local view does.
#[test]
fn general_store_round_trips_and_priority_only_touch_the_batch() {
    for related in [false, true] {
        let mut samples = Vec::new();
        for size in [32, 128, 512] {
            let root = PureFactStore::from_ordered(
                &(0..size)
                    .map(|index| fact(index, related))
                    .collect::<Vec<_>>(),
            );
            let before_lists = fact_list_entry_counts();
            let _ = crate::kernel::proof::take_fact_entry_counts();
            let before_contexts = crate::kernel::reasoning::path_facts::context_rebuild_entries();
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                for index in 0..size {
                    let selected = fact(index, related);
                    let added = fact(size + index, related);
                    let child = root.with_statement_facts(vec![selected.clone(), added.clone()]);
                    let view = PureFactList::from_store(&child);
                    assert_eq!(view.get(0), Some(&selected));
                    assert_eq!(view.get(1), Some(&added));
                    let copy = PureFactList::from_source(&view);
                    let retained = PureFactStore::from_source(&copy);
                    let forwarded = std::sync::Arc::new(&copy);
                    assert!(forwarded.fact_store().shares_assumptions_with(&retained));
                    assert!(retained.shares_assumptions_with(&child));
                    assert!(retained.shares_exact_index_with(&child));
                    assert!(!root.contains(&added));
                    let mut duplicates = copy;
                    duplicates.push(selected.clone());
                    assert_eq!(duplicates.get(duplicates.len() - 1), Some(&selected));
                    assert!(duplicates.fact_store().shares_assumptions_with(&child));
                }
            });
            samples.push(work);
            assert_eq!(fact_list_entry_counts(), before_lists);
            assert_eq!(
                crate::kernel::proof::take_fact_entry_counts(),
                (size as usize, 0)
            );
            assert_eq!(
                crate::kernel::reasoning::path_facts::context_rebuild_entries(),
                before_contexts
            );
        }
        assert!(
            samples.windows(2).all(|pair| pair[1] <= pair[0] * 6 + 1024),
            "{samples:?}"
        );
    }
}
