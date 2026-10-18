// Scaling tests of `src/kernel/tests/contract_execution_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn certification_of_algebraic_witness_ignores_unrelated_quantifiers() {
    let mut samples = Vec::new();
    for size in [32, 64, 128, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = AlgebraicType::parameter("Path".into());
        let memory = CMemory::new().with_block("graph", 4);
        let mut facts = PureFactContext::new().assume_proposition(path_exists_at_snapshot(
            &ty,
            100,
            100,
            memory.clone(),
            0,
        ));
        for i in 1..=size {
            facts = facts.assume_proposition(path_exists_at_snapshot(
                &ty,
                1_000 + u64::from(i),
                1_000 + u64::from(i),
                memory.clone(),
                i,
            ));
        }
        facts.build_stated_proposition_index();
        let goal = path_exists_at_snapshot(&ty, 200, 200, memory.clone(), 0);
        let missing = path_exists_at_snapshot(&ty, 200, 200, memory, 1_000);
        let (verdicts, work) = crate::instrumentation::measure_deterministic_work(|| {
            (
                crate::kernel::PureFactContext::settles_exactly(&facts, &goal),
                crate::kernel::PureFactContext::settles_exactly(&facts, &missing),
            )
        });
        assert_eq!(verdicts, (true, false));
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "certification scanned unrelated quantifiers: {samples:?}"
    );
}

#[test]
fn conditional_universal_certification_ignores_unrelated_facts() {
    let mut samples = Vec::new();
    for size in [32, 64, 128, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = AlgebraicType::parameter("Path".into());
        let memory = CMemory::new().with_block("graph", 4);
        let mut facts = PureFactContext::new().assume_proposition(conditional_path_universal(
            &ty,
            100,
            memory.clone(),
            0,
        ));
        let mut proof_facts =
            crate::kernel::proof::ProofFacts::from_ordered(&[conditional_path_universal(
                &ty,
                100,
                memory.clone(),
                0,
            )]);
        for i in 1..=size {
            proof_facts = proof_facts.with_kernel_checked_fact(conditional_path_universal(
                &ty,
                1_000 + 2 * u64::from(i),
                memory.clone(),
                i,
            ));
            facts = facts.assume_proposition(conditional_path_universal(
                &ty,
                1_000 + 2 * u64::from(i),
                memory.clone(),
                i,
            ));
        }
        facts.build_stated_proposition_index();
        let goal = conditional_path_universal(&ty, 200, memory.clone(), 0);
        let missing = conditional_path_universal(&ty, 200, memory, 1_000);
        let (verdicts, work) = crate::instrumentation::measure_deterministic_work(|| {
            (
                crate::kernel::PureFactContext::settles_exactly(&facts, &goal),
                crate::kernel::PureFactContext::settles_exactly(&facts, &missing),
                proof_facts.pure_assumption_available(&goal),
                proof_facts.pure_assumption_available(&missing),
            )
        });
        assert_eq!(verdicts, (true, false, true, false));
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "conditional lookup scanned unrelated facts: {samples:?}"
    );
}

#[test]
fn reassociated_signed_add_domain_requires_each_guard_and_scales() {
    let a = Bitvector32Term::Variable(Variable(960_170));
    let b = Bitvector32Term::Variable(Variable(960_171));
    let c = Bitvector32Term::Variable(Variable(960_172));
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_add_overflows(a.clone(), Bitvector32Term::add(b.clone(), c.clone())),
        false,
    );
    let guards = [
        ConditionTerm::signed_add_overflows(a.clone(), b.clone()),
        ConditionTerm::signed_add_overflows(Bitvector32Term::add(a.clone(), b.clone()), c.clone()),
        ConditionTerm::signed_add_overflows(b.clone(), c.clone()),
    ];
    for missing in 0..3 {
        let mut facts = PureFactContext::new();
        for (index, guard) in guards.iter().enumerate() {
            if index != missing {
                facts = facts.assume_condition(guard.clone(), false);
            }
        }
        assert!(
            !crate::kernel::api::checked_int32_reassociated_add_domain(&facts, &goal),
            "missing domain {missing} was accepted"
        );
    }
    let work = [16, 64, 256].map(|size| {
        let mut facts = PureFactContext::new();
        for index in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(961_000 + index)),
                    Bitvector32Term::Constant(index as u32),
                ),
                true,
            );
        }
        for guard in &guards {
            facts = facts.assume_condition(guard.clone(), false);
        }
        let (accepted, work) = crate::persistent::measure_persistent_work(|| {
            crate::kernel::api::checked_int32_reassociated_add_domain(&facts, &goal)
        });
        assert!(accepted);
        work
    });
    assert!(work[0] > 0);
    assert!(
        work.iter().all(|sample| *sample <= work[0] + 256),
        "regrouping scanned unrelated facts: {work:?}"
    );
    // The sequential total can be in range while the regrouped inner sum
    // overflows: MIN + MAX + 1 == 0 is not a license to evaluate MAX + 1.
    let a = Bitvector32Term::Constant(i32::MIN as u32);
    let b = Bitvector32Term::Constant(i32::MAX as u32);
    let c = Bitvector32Term::Constant(1);
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_add_overflows(a, Bitvector32Term::add(b, c)),
        false,
    );
    assert!(!crate::kernel::api::checked_int32_reassociated_add_domain(
        &PureFactContext::new(),
        &goal
    ));
}

// Scalar allocation and access must not scan unrelated memory or holdings.
#[test]
fn automatic_scalar_ownership_work_is_independent_of_unrelated_storage() {
    let mut measurements = Vec::new();
    for count in [0u32, 16, 64, 256] {
        let mut memory = CMemory::new();
        let mut resources = ResourceContext::new();
        for index in 0..count {
            let pointer = Pointer {
                block: format!("global:unrelated:{index}").into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            memory = memory
                .with_block(pointer.block.clone(), 4)
                .store(pointer.clone(), uint32(index));
            resources = resources.unchecked_with_fact(CResourceFact::own_memory(
                CMemoryRange::new_with_element_width(pointer, 0.into(), 4.into(), 1),
            ));
        }
        let state = CState::new()
            .with_memory(memory)
            .with_resource_context(resources);
        let statement = c_seq(
            c_declare("word", CType::UInt32),
            c_seq(
                c_assign("word", c_uint32_literal(7)),
                c_return(c_variable("word")),
            ),
        );
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            execute_c_statement_paths(
                &state,
                &statement,
                &PureFactContext::new(),
                CExecutionContext::execute_bodies(&CExecutionEnvironment::new()),
                &mut ExecutionBudget::new(),
            )
            .unwrap()
        });
        assert!(
            matches!(&paths[0].outcome, CStatementOutcome::Return { value: CValue::UInt32(value), .. } if value.as_const() == Some(7))
        );
        measurements.push(work);
    }
    assert!(
        measurements
            .iter()
            .all(|work| *work <= measurements[0].max(1) * 4 + 32),
        "unrelated storage changed scalar allocation/access work: {measurements:?}"
    );
    {
        let costs = measurements.clone();
        let indexed = |costs: &[usize]| costs.iter().all(|work| *work <= costs[0] + 64);
        assert!(indexed(&costs), "indexed work: {costs:?}");
        let scanned = costs
            .iter()
            .zip([0u32, 16, 64, 256])
            .map(|(work, size)| work + usize::try_from(size).unwrap())
            .collect::<Vec<_>>();
        assert!(
            !indexed(&scanned),
            "the smaller fixture must detect a visit per unrelated item: {costs:?}"
        );
    }
}
