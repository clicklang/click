// Scaling tests of `src/kernel/tests/canonicalization_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// Collecting the variables of a load counts each snapshot the load reaches
/// once, not once per path to it. Each level of the DAG is reached through
/// two cells of the level above, so walking it as a tree visited `2^depth`
/// snapshots, uncharged; depth 32 did not finish.
#[test]
fn variable_collection_walks_a_shared_snapshot_dag_once() {
    let samples = [8usize, 16, 32, 64].map(|depth| {
        let load = nested_snapshot_load(depth);
        crate::kernel::reasoning::variable_collection::clear_shared_memory_variables();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut variables = BTreeSet::new();
            crate::kernel::reasoning::collect_bitvector_variables(&load, &mut variables);
        });
        (depth, work)
    });
    for (depth, work) in samples {
        assert!(work >= depth, "counting a snapshot is charged: {samples:?}");
    }
    for pair in samples.windows(2) {
        let ((_, work), (_, next_work)) = (pair[0], pair[1]);
        assert!(
            next_work <= 2 * work + 8,
            "collection should be linear in the DAG depth: {samples:?}"
        );
    }
}

/// A snapshot one store past a counted one is counted from that one's
/// variables by the entries the store changed, not by walking every cell:
/// collecting the variables of a load after the store costs the same beside
/// 16 to 1024 unrelated cells. Counting each reached snapshot whole made the
/// collection linear in the unrelated cells, which is what made a round
/// trip's extra copy grow with the unrelated allocations beside it.
#[test]
fn variable_collection_after_a_store_costs_the_store() {
    let block = PointerBlock::Concrete("counted-history".to_string());
    let at = |offset: i64| Pointer {
        block: block.clone(),
        offset: PointerOffsetTerm::Constant(offset),
    };
    let samples = [16usize, 64, 256, 1024].map(|cells| {
        let mut memory = CMemory::new().with_block("counted-history", 4 * cells as u32 + 8);
        for index in 0..cells {
            memory = memory.store(
                at(4 * index as i64),
                CValue::Int32(Bitvector32Term::Variable(Variable(
                    7_000_000 + index as u64,
                ))),
            );
        }
        let before = crate::kernel::intern_c_memory(memory.clone());
        crate::kernel::reasoning::variable_collection::clear_shared_memory_variables();
        let mut variables = BTreeSet::new();
        crate::kernel::reasoning::collect_bitvector_variables(
            &Bitvector32Term::MemoryLoad(before, Box::new(at(0)), crate::kernel::LoadKind::Bits32),
            &mut variables,
        );
        assert_eq!(variables.len(), cells);
        let after = memory.store(
            at(0),
            CValue::Int32(Bitvector32Term::Variable(Variable(7_900_000))),
        );
        let load = Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(after),
            Box::new(at(4)),
            crate::kernel::LoadKind::Bits32,
        );
        let (variables, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut variables = BTreeSet::new();
            crate::kernel::reasoning::collect_bitvector_variables(&load, &mut variables);
            variables
        });
        assert!(variables.contains(&Variable(7_900_000)));
        assert!(
            !variables.contains(&Variable(7_000_000)),
            "the overwritten cell's variable leaves"
        );
        assert_eq!(variables.len(), cells);
        (cells, work)
    });
    let (_, first) = samples[0];
    assert!(
        samples.iter().all(|(_, work)| *work <= first + 4),
        "a store's collection grows with unrelated cells: {samples:?}"
    );
}

/// The same for a store into a symbolic static array: its elements are one
/// run whose slots mention no variable but their own load variables, and a
/// collection leaves those out rather than naming every slot to find them,
/// so neither a collection nor a store's collection grows with the array or
/// mints a load identity. The stored value's variable arrives with the store.
#[test]
fn variable_collection_after_a_store_into_a_symbolic_array_costs_the_store() {
    let block = PointerBlock::Concrete("symbolic-array-history".to_string());
    let at = |offset: i64| Pointer {
        block: block.clone(),
        offset: PointerOffsetTerm::Constant(offset),
    };
    let samples = [16u32, 64, 256, 1024, 1_000_000].map(|elements| {
        let _session = crate::kernel::VerificationSession::enter();
        let size = 4 * elements;
        let source = crate::kernel::intern_c_memory(
            CMemory::new().with_block_without_derivation(block.clone(), size),
        );
        let Ok(memory) = CMemory::new()
            .with_block("symbolic-array-history", size)
            .with_symbolic_storage_run(at(0), CType::Int32, elements, source)
        else {
            panic!("a symbolic array over a fresh block is one run");
        };
        let before = crate::kernel::intern_c_memory(memory.clone());
        let registered = crate::kernel::eval::load_variable_registry_len();
        let (variables, entry_work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut variables = BTreeSet::new();
            crate::kernel::reasoning::collect_bitvector_variables(
                &Bitvector32Term::MemoryLoad(
                    before,
                    Box::new(at(0)),
                    crate::kernel::LoadKind::Bits32,
                ),
                &mut variables,
            );
            variables
        });
        assert!(
            variables.is_empty(),
            "an unread element contributes no variable: {variables:?}"
        );
        assert_eq!(
            crate::kernel::eval::load_variable_registry_len(),
            registered,
            "collecting a symbolic array's variables names none of its elements"
        );
        let after = memory.clone().store(
            at(0),
            CValue::Int32(Bitvector32Term::Variable(Variable(7_900_000))),
        );
        let load = Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(after),
            Box::new(at(4)),
            crate::kernel::LoadKind::Bits32,
        );
        let registered = crate::kernel::eval::load_variable_registry_len();
        let (variables, store_work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut variables = BTreeSet::new();
            crate::kernel::reasoning::collect_bitvector_variables(&load, &mut variables);
            variables
        });
        assert_eq!(variables, BTreeSet::from([Variable(7_900_000)]));
        assert_eq!(
            crate::kernel::eval::load_variable_registry_len(),
            registered,
            "a store's collection names none of the array's elements"
        );
        (elements, entry_work, store_work)
    });
    let (_, first_entry, first_store) = samples[0];
    assert!(
        samples
            .iter()
            .all(|(_, entry, store)| *entry == first_entry && *store == first_store),
        "a collection grows with the array's other elements: {samples:?}"
    );
}
