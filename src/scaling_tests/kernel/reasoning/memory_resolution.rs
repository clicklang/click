// Scaling tests of `src/kernel/reasoning/memory_resolution.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[cfg(test)]
#[test]
fn memory_resolution_graph_offset_queries_scale_without_legacy_fact_index() {
    for size in [16u64, 64, 256, 1024] {
        let scalar = |id| Bitvector32Term::Variable(Variable(92_000 + id));
        let offset = |id| PointerOffsetTerm::scale_int32(scalar(id), 4);
        let named = PointerOffsetTerm::Variable(Variable(94_000));
        let mut context = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_offset_equal(offset(0), named.clone()),
            true,
        );
        for index in 0..size {
            context = context
                .assume_condition(ConditionTerm::equal(scalar(index), scalar(index + 1)), true);
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                assert_eq!(
                    pointer_offsets_equal_for_memory_resolution(&offset(index), &named, &context),
                    Some(true)
                );
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 200 * size as usize, "size={size}, work={work}");
    }
}

#[cfg(test)]
#[test]
fn stored_load_alias_lookup_ignores_unrelated_cells() {
    let target = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(8_991_001)), 4),
    };
    let alias = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(8_991_002)), 4),
    };
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_offset_equal(target.offset.clone(), alias.offset.clone()),
        true,
    );
    let mut samples = Vec::new();
    for count in [8, 32, 128, 512] {
        let mut memory = CMemory::new();
        for index in 0..count {
            memory = memory.store(
                Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::Constant(index * 4),
                },
                CValue::Int32(Bitvector32Term::Constant(0)),
            );
        }
        // Snapshot construction/interning belongs to the producer. Measure
        // only a lookup in the already established snapshot.
        crate::kernel::intern_c_memory_ref(&memory);
        let (absent, work) = crate::instrumentation::measure_deterministic_work(|| {
            stored_value_at_equal_pointer(&memory, &target, &assumptions)
        });
        assert!(absent.is_none());
        samples.push(work);
        let value = CValue::Int32(Bitvector32Term::Constant(17));
        memory = memory.store(alias.clone(), value.clone());
        assert_eq!(
            stored_value_at_equal_pointer(&memory, &target, &assumptions),
            Some(value)
        );
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 16),
        "{samples:?}"
    );
}

#[cfg(test)]
#[test]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn interior_base_alias_frames_only_distinct_objects_and_is_indexed() {
    let base = Pointer {
        block: PointerBlock::Heap(920_000),
        offset: PointerOffsetTerm::Constant(0),
    };
    let alias = Pointer {
        block: PointerBlock::Symbolic(Variable(920_001)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let local = Pointer {
        block: "local:interior-alias-store".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let equality = ConditionTerm::pointer_equal(alias.clone(), base.clone());
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut facts = PureFactContext::new();
        for index in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::pointer_equal(
                    Pointer {
                        block: PointerBlock::Symbolic(Variable(930_000 + index)),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    Pointer {
                        block: PointerBlock::Heap(940_000 + index),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                ),
                true,
            );
        }
        let absent = facts.clone();
        facts = facts.assume_condition(equality.clone(), true);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for offset in [-1i64, 0, 1, 2, 3, 16] {
                let read = Pointer {
                    offset: PointerOffsetTerm::Constant(offset),
                    ..alias.clone()
                };
                assert!(pointers_proven_distinct_for_memory_resolution(
                    &local, &read, &facts
                ));
                assert!(
                    crate::kernel::memory_provenance::write_access_is_disjoint_from_load(
                        &local, 4, &read, 4, &facts
                    )
                );
            }
        });
        samples.push((size, work));
        let interior = Pointer {
            offset: PointerOffsetTerm::Constant(1),
            ..alias.clone()
        };
        assert!(!pointers_proven_distinct_for_memory_resolution(
            &local, &interior, &absent
        ));
        let withdrawn = facts.without_exact_fact(&Proposition::ConditionIs(equality.clone(), true));
        assert!(!pointers_proven_distinct_for_memory_resolution(
            &local, &interior, &withdrawn
        ));
        // Different starting addresses in the same object are insufficient
        // evidence for either an exact interior alias or a multi-byte frame.
        assert!(!pointers_proven_distinct_for_memory_resolution(
            &base, &interior, &facts
        ));
        assert!(
            !crate::kernel::memory_provenance::write_access_is_disjoint_from_load(
                &base, 4, &interior, 4, &facts
            )
        );
    }
    eprintln!("interior alias frame (N, units): {samples:?}");
    let baseline = samples[0].1;
    assert!(
        samples.iter().all(|(_, work)| *work <= baseline + 256),
        "interior alias framing scanned unrelated facts: {samples:?}"
    );
}

#[cfg(test)]
#[test]
fn mixed_index_offsets_work_ignores_unrelated_facts() {
    use crate::kernel::{IntegerTerm, MachineIntegerType};
    let wide = Bitvector32Term::Variable(Variable(82001));
    let narrow = Bitvector32Term::Variable(Variable(82002));
    let native = PointerOffsetTerm::scale_int64(wide.clone(), 1, true);
    let signed = PointerOffsetTerm::scale_int32(narrow.clone(), 1);
    let fact = ConditionTerm::IntegerEqual(
        IntegerTerm::from_machine(MachineIntegerType::UInt64, wide)
            .unwrap()
            .into(),
        IntegerTerm::from_machine(MachineIntegerType::Int32, narrow)
            .unwrap()
            .into(),
    );
    let mut counts = Vec::new();
    for size in [32, 128, 512] {
        let mut context = PureFactContext::new().assume_condition(fact.clone(), true);
        for i in 0..size {
            context = context.assume_condition(
                ConditionTerm::IntegerEqual(
                    IntegerTerm::Variable(Variable(83000 + i)).into(),
                    IntegerTerm::constant_i64(i as i64).into(),
                ),
                true,
            );
        }
        let (answer, units) = crate::instrumentation::measure_deterministic_work(|| {
            mixed_index_offsets_equal(&native, &signed, &context)
        });
        assert_eq!(answer, Some(true));
        counts.push(units);
    }
    assert_eq!(counts[0], counts[1]);
    assert_eq!(counts[1], counts[2]);
    assert!(counts[0] > 0);
}
