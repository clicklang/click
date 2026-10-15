// Scaling tests of `src/kernel/tests/expression_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn wide_equality_bounds_use_incremental_index_and_preserve_branches() {
    for size in [16usize, 64, 256, 1024] {
        let start = crate::persistent::persistent_node_allocations();
        let mut facts = PureFactContext::new();
        for i in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::uint64_equal(
                    Bitvector32Term::Variable(Variable(1000 + i as u64)),
                    Bitvector32Term::UInt64Constant(i as u64),
                ),
                true,
            );
        }
        let allocations = crate::persistent::persistent_node_allocations() - start;
        assert!(
            allocations < 80 * size * (size.ilog2() as usize + 1),
            "{size}: {allocations}"
        );
        let target = Bitvector32Term::Variable(Variable(1000));
        let bound =
            ConditionTerm::uint64_less_equal(target.clone(), Bitvector32Term::UInt64Constant(1));
        let (answer, work) =
            crate::instrumentation::measure_deterministic_work(|| facts.decide(&bound));
        assert_eq!(answer, Some(true));
        assert!(
            work <= 16,
            "unrelated equalities inflated query work: {size}: {work}"
        );
        let original = facts.clone();
        let equality = ConditionTerm::uint64_equal(target, Bitvector32Term::UInt64Constant(0));
        let changed = facts.assume_condition(equality, false);
        assert_eq!(changed.decide(&bound), None);
        assert_eq!(original.decide(&bound), Some(true));
    }
}

#[test]
fn loadable_object_provenance_lookup_ignores_unrelated_external_pointers() {
    let external = |variable| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(variable))),
            byte_width: 4,
        },
    };
    let target = external(31_070);
    let loadable = |base| Proposition::CMemoryLoadable {
        memory: CMemory::new(),
        base,
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    };

    let samples = [4usize, 16, 64, 256]
        .into_iter()
        .map(|size| {
            let mut assumptions =
                PureFactContext::new().assume_proposition(loadable(target.clone()));
            for index in 0..size {
                assumptions =
                    assumptions.assume_proposition(loadable(external(32_000 + index as u64)));
            }
            let (count, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions
                    .memory_loadable_candidates_for_object(&target)
                    .count()
            });
            assert_eq!(count, 1);
            work
        })
        .collect::<Vec<_>>();
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "object-provenance lookup scanned unrelated external pointers: {samples:?}"
    );
}

#[test]
fn exact_signed_constant_bound_lookup_ignores_unrelated_facts() {
    let value = Bitvector32Term::Variable(Variable(87_901));
    let query = ConditionTerm::signed_greater_than(value.clone(), Bitvector32Term::Constant(1));
    let mut samples = Vec::new();
    for size in [64, 256, 1024] {
        let mut assumptions = PureFactContext::new().assume_condition(
            ConditionTerm::signed_greater_equal(value.clone(), Bitvector32Term::Constant(2)),
            true,
        );
        for index in 0..size {
            assumptions = assumptions.assume_condition(
                ConditionTerm::signed_greater_equal(
                    Bitvector32Term::Variable(Variable(90_000 + index)),
                    Bitvector32Term::Constant(2),
                ),
                true,
            );
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            assumptions.decide_condition_for_simp(&query)
        });
        assert_eq!(result, Some(true));
        samples.push(work);
    }
    assert!(
        samples[2] <= samples[0].saturating_mul(2) + 10,
        "{samples:?}"
    );
}

#[test]
fn exact_signed_mirror_normalization_ignores_unrelated_facts() {
    let value = Bitvector32Term::Variable(Variable(87_910));
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(1), value.clone()),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(value, Bitvector32Term::Constant(1)),
        true,
    );
    let mut samples = Vec::new();
    for size in [64, 256, 1024] {
        let mut premises = vec![premise.clone()];
        for index in 0..size {
            premises.push(Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(
                    Bitvector32Term::Variable(Variable(91_000 + index)),
                    Bitvector32Term::Constant(2),
                ),
                true,
            ));
        }
        let facts = crate::kernel::proof::ProofFacts::from_ordered(&premises);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::proof::fact_reasoning::normalize_using_conditions(
                &goal,
                std::slice::from_ref(&premise),
                &facts,
            )
        });
        assert!(result.is_ok());
        samples.push(work);
    }
    assert!(
        samples[2] <= samples[0].saturating_mul(2) + 10,
        "{samples:?}"
    );
}

#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn resource_object_provenance_does_not_scan_same_raw_block() {
    let pointer = |id| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(895_000 + id)),
    };
    let target = pointer(0);
    let expression = c_less_equal(c_variable("pointer"), c_variable("pointer"));
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let assumptions = PureFactContext::new();
        let mut resources = ResourceContext::new_with_equalities(&assumptions);
        for id in 1..=size {
            resources = resources.unchecked_with_fact(CResourceFact::view_memory(
                CMemoryRange::new_with_element_width(pointer(id), 0u32.into(), 4u32.into(), 1),
            ));
        }
        resources = resources.unchecked_with_fact(CResourceFact::view_memory(
            CMemoryRange::new_with_element_width(target.clone(), 0u32.into(), 4u32.into(), 1),
        ));
        let state = CState::new()
            .with_local("pointer", CValue::pointer(target.clone()))
            .with_resource_context(resources);
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut budget = ExecutionBudget::for_c_expression(&expression);
            evaluate_c_expression_paths(&state, &expression, &assumptions, &mut budget).unwrap()
        });
        assert!(
            paths
                .iter()
                .all(|path| matches!(path.outcome, CExpressionOutcome::Value(_)))
        );
        samples.push(work);
    }
    assert!(
        samples[3] <= samples[0] + 2000,
        "provenance scanned the raw block: {samples:?}"
    );
}
