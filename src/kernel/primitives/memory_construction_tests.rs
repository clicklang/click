use super::*;

fn assert_explained(memory: &CMemory) {
    let mut pending = vec![memory.clone()];
    let mut seen = std::collections::HashSet::new();
    while let Some(memory) = pending.pop() {
        if !seen.insert(memory.diagnostic_identity()) {
            continue;
        }
        match memory.diagnostic_construction() {
            Some(CMemoryConstructionKind::Transition(edge)) => {
                pending.push(edge.base().memory().clone());
                if let CMemoryDerivation::CellsSeeded { run, .. } = edge.as_ref() {
                    pending.push(run.source().memory().clone());
                }
            }
            Some(CMemoryConstructionKind::Transform { sources, .. }) => {
                assert!(!sources.is_empty());
                pending.extend(sources.iter().cloned());
            }
            None => assert!(memory.is_initial_diagnostic_memory(), "unexplained memory"),
        }
        assert!(seen.len() < 100, "unexpected construction cycle");
    }
}

#[test]
fn memory_constructions_cover_non_transition_producers() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Pointer {
        block: "local:construction".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new()
        .with_block("local:construction", 16)
        .store(pointer.clone(), CValue::Int32(7.into()));
    let projected = crate::kernel::memory_provenance::canonical_c_memory_for_pointer_load(
        &memory,
        &Pointer::symbolic(Variable(990_810)),
    );
    assert!(matches!(
        projected.diagnostic_construction(),
        Some(CMemoryConstructionKind::Transform {
            operation: "project memory for pointer read",
            ..
        })
    ));
    let variants = [
        projected,
        crate::kernel::memory_provenance::canonical_c_memory_deep(&memory),
        memory.without_cell(&pointer),
        memory.clone().with_uninitialized_object(pointer.clone(), 4),
        memory.clone().with_block_without_derivation("synthetic", 4),
        memory.clone().with_block("havoc:990811", 0),
        memory
            .clone()
            .store_union(pointer.clone(), CType::Int32, CValue::Int32(8.into())),
        crate::kernel::reasoning::substitute_pointer_variable_in_memory(
            &memory,
            Variable(990_810),
            &pointer,
        ),
        memory
            .clone()
            .with_interface_memory_havoc_preserving_loans(
                Variable(990_812),
                &BTreeSet::new(),
                &[&memory],
                None,
            )
            .unwrap(),
    ];
    for memory in variants {
        assert_explained(&memory);
    }
}

#[test]
fn construction_metadata_does_not_change_memory_identity_or_proof_edges() {
    let _session = crate::kernel::VerificationSession::enter();
    let original = CMemory::new().with_block("local:identity", 4);
    let interned = intern_c_memory_ref(&original);
    let mut described = original.clone();
    // A distinct diagnostic path describes exactly the same semantic snapshot.
    described.record_diagnostic_transform("diagnostic test", vec![CMemory::new()], Vec::new());
    assert_eq!(original, described);
    assert_eq!(
        c_memory_content_hash(&original),
        c_memory_content_hash(&described)
    );
    assert_eq!(interned, intern_c_memory_ref(&described));
    assert_eq!(
        interned.read_identity(),
        intern_c_memory_ref(&described).read_identity()
    );
    assert_eq!(interned.derivation().unwrap().kind_name(), "BlockDeclared");
}

#[test]
fn construction_recording_cost_is_independent_of_snapshot_size() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut costs = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut memory = CMemory::new();
        for i in 0..size {
            memory = memory.store(
                Pointer {
                    block: "local:scale".into(),
                    offset: PointerOffsetTerm::Constant(i * 4),
                },
                CValue::Int32((i as u32).into()),
            );
        }
        let (_, cost) = crate::instrumentation::measure_deterministic_work(|| {
            memory.record_diagnostic_transform("diagnostic test", vec![CMemory::new()], Vec::new());
        });
        costs.push(cost);
    }
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}

#[test]
fn unrecorded_mutation_cannot_inherit_an_incorrect_origin() {
    let original = CMemory::new().with_block("local:changed", 4);
    let mut changed = original.clone();
    Arc::make_mut(&mut changed.blocks).insert("local:extra".into(), CBlock::new(4));
    assert!(changed.diagnostic_construction().is_none());
    assert!(original.diagnostic_construction().is_some());
}

#[test]
fn construction_pins_detect_mutation_of_an_uninterned_snapshot() {
    let pointer = Pointer {
        block: "local:unpinned".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut memory = CMemory::new().with_uninitialized_object(pointer.clone(), 4);
    assert!(memory.diagnostic_construction().is_some());
    Arc::make_mut(&mut memory.heap)
        .uninitialized_objects
        .insert(pointer, 8);
    assert!(memory.diagnostic_construction().is_none());
}
