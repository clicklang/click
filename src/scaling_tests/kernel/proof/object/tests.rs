// Scaling tests of `src/kernel/proof/object.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn invariant_body_evidence_requires_exact_complete_root_and_context() {
    use crate::kernel::proof::{
        ExecutionFrontier, ExecutionProofCore, ExecutionRegionKind, FrontierPosition,
    };
    use crate::kernel::{
        CComparisonOperator, CLoopInvariantCheck, CState, CValue, SpecExpression, SpecProposition,
    };
    type TestProof =
        ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ProofExecutionState<()>>;
    let root = |facts: ProofFacts, core: ExecutionProofCore| -> TestProof {
        ProofObject::root(
            (),
            ProofBranch::new(
                ProofObligation::Frontier(FrontierObligation),
                ProofBranchState {
                    facts,
                    unfolded_predicates: PersistentOrderedSet::default(),
                    execution: Some(Arc::new(ProofExecutionState::new(core, ()))),
                },
            ),
        )
    };
    let checks = [0, 1].map(|value| {
        CLoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(value))),
                operator: CComparisonOperator::LessEqual,
                right: SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(value))),
            },
            None,
            None,
        )
    });
    let entry = CState::new();
    let samples = [16, 32, 64, 128].map(|size| {
        let facts = ProofFacts::from_ordered(
            &(0..size)
                .map(|i| Proposition::Predicate {
                    name: format!("unrelated_{i}"),
                    arguments: vec![],
                })
                .collect::<Vec<_>>(),
        );
        let core = ExecutionProofCore::at_entry(
            CState::new(),
            ExecutionFrontier {
                region: ExecutionRegionKind::LoopBody,
                position: FrontierPosition::RegionBoundary,
                ..Default::default()
            },
        );
        let frontier = root(facts.clone(), core);
        let ((body, scope), opening_work) =
            crate::instrumentation::measure_deterministic_work(|| {
                frontier
                    .open_invariant_body(&entry, &entry, &checks, &[], &[], &[], |_, _| ())
                    .unwrap()
            });
        assert!(
            frontier
                .retain_invariant_body(scope.clone(), &body)
                .is_err()
        );
        // Even the same exact goal and premises in a fresh root are not this scope.
        let unrelated = TestProof::root((), body.state.open_branches.root_branch().clone())
            .apply_normalize()
            .ok()
            .unwrap();
        assert!(
            frontier
                .retain_invariant_body(scope.clone(), &unrelated)
                .is_err()
        );
        let complete = body.apply_normalize().ok().unwrap();
        let (closed, closing_work) = crate::instrumentation::measure_deterministic_work(|| {
            let closed = frontier
                .retain_invariant_body(scope.clone(), &complete)
                .unwrap();
            closed
                .validate_checked_invariant_lowerings(&checks, &[])
                .unwrap();
            closed
        });
        assert!(
            closed
                .validate_checked_invariant_lowerings(&checks[..1], &[])
                .is_err()
        );
        let core = closed.execution_view().unwrap().execution().core.clone();
        for variant in 0..4 {
            let mut changed = core.clone();
            let mut changed_facts = facts.clone();
            match variant {
                0 => changed.state = CState::new().into(),
                1 => changed.effect_facts = Vec::new().into(),
                2 => {
                    changed_facts = facts.with_fact(Proposition::Predicate {
                        name: "other_arm".into(),
                        arguments: vec![],
                    })
                }
                _ => {
                    Arc::make_mut(changed.checked_invariant_lowerings.as_mut().unwrap()).body = None
                }
            }
            let stale = root(changed_facts, changed);
            assert!(
                stale
                    .validate_checked_invariant_lowerings(&checks, &[])
                    .is_err()
            );
            if variant < 3 {
                assert!(
                    stale
                        .retain_invariant_body(scope.clone(), &complete)
                        .is_err()
                );
            }
        }
        let mut wrong = core;
        Arc::make_mut(wrong.checked_invariant_lowerings.as_mut().unwrap())
            .body
            .as_mut()
            .unwrap()
            .goal = Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(false), true);
        assert!(
            root(facts, wrong)
                .validate_checked_invariant_lowerings(&checks, &[])
                .is_err()
        );
        opening_work + closing_work
    });
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0].saturating_mul(2).saturating_add(8),
            "{samples:?}"
        );
    }
}

#[test]
fn invariant_bundle_closure_checks_retained_evidence_and_context_locally() {
    use crate::kernel::proof::{
        ExecutionFrontier, ExecutionProofCore, ExecutionRegionKind, FrontierPosition,
    };
    use crate::kernel::{
        CComparisonOperator, CLoopInvariantCheck, CState, CValue, SpecExpression, SpecProposition,
    };
    type TestProof =
        ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ProofExecutionState<()>>;
    // One entry state: every snapshot below must be the very same state,
    // creation ledger included.
    let entry = CState::new().with_population_creation_tracking();
    let root = |facts: ProofFacts, core: ExecutionProofCore| -> TestProof {
        ProofObject::root(
            (),
            ProofBranch::new(
                ProofObligation::Frontier(FrontierObligation),
                ProofBranchState {
                    facts,
                    unfolded_predicates: PersistentOrderedSet::default(),
                    execution: Some(Arc::new(ProofExecutionState::new(core, ()))),
                },
            ),
        )
    };
    let checks = vec![
        CLoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(0))),
                operator: CComparisonOperator::LessEqual,
                right: SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(0))),
            },
            None,
            None,
        ),
        CLoopInvariantCheck::new(
            SpecProposition::Predicate {
                resource_state_dependent: true,
                name: "invariant".into(),
                arguments: vec![],
            },
            None,
            None,
        ),
    ];
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let facts = ProofFacts::from_ordered(
            &(0..size)
                .map(|i| Proposition::Predicate {
                    name: format!("unrelated_{i}"),
                    arguments: vec![],
                })
                .collect::<Vec<_>>(),
        )
        .with_fact(Proposition::Predicate {
            name: "invariant".into(),
            arguments: vec![Term::CState(Box::new(entry.resource_state_snapshot()))],
        });
        let core = ExecutionProofCore::at_entry(
            entry.clone(),
            ExecutionFrontier {
                region: ExecutionRegionKind::LoopBody,
                position: FrontierPosition::RegionBoundary,
                ..Default::default()
            },
        );
        let unprepared = root(facts.clone(), core);
        assert!(
            unprepared
                .validate_checked_invariant_lowerings(&checks, &[])
                .is_err()
        );
        let requested = unprepared
            .request_frontier_invariant_closure()
            .ok()
            .unwrap();
        assert!(
            requested
                .validate_checked_invariant_lowerings(&checks, &[])
                .is_err()
        );
        let (body, scope) = unprepared
            .open_invariant_body(
                &entry.clone(),
                &entry.clone(),
                &checks,
                &[],
                &[],
                &[],
                |_, _| (),
            )
            .unwrap();
        let completed = body.apply_normalize().ok().unwrap();
        let prepared = unprepared.retain_invariant_body(scope, &completed).unwrap();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            prepared.validate_checked_invariant_lowerings(&checks, &[])
        });
        result.unwrap();
        samples.push(work);
        assert!(
            prepared
                .validate_checked_invariant_lowerings(&[], &[])
                .is_err()
        );
        let changed_checks = vec![CLoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(1))),
                operator: CComparisonOperator::LessEqual,
                right: SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(1))),
            },
            None,
            None,
        )];
        assert!(
            prepared
                .validate_checked_invariant_lowerings(&changed_checks, &[])
                .is_err()
        );
        let core = prepared.execution_view().unwrap().execution().core.clone();
        let mut stale_effects = core.clone();
        stale_effects.effect_facts = Vec::new().into();
        assert!(
            root(facts.clone(), stale_effects)
                .validate_checked_invariant_lowerings(&checks, &[])
                .is_err()
        );
        let mut stale = core.clone();
        // Even an equal-valued replacement snapshot is not the saved one.
        stale.state = CState::new().with_population_creation_tracking().into();
        assert!(
            root(facts.clone(), stale)
                .validate_checked_invariant_lowerings(&checks, &[])
                .is_err()
        );
        let other_facts = facts.with_fact(Proposition::Predicate {
            name: "other_arm".into(),
            arguments: vec![],
        });
        assert!(
            root(other_facts, core.clone())
                .validate_checked_invariant_lowerings(&checks, &[])
                .is_err()
        );
        let mut incomplete = core.clone();
        Arc::make_mut(incomplete.checked_invariant_lowerings.as_mut().unwrap()).body = None;
        assert!(
            root(facts.clone(), incomplete)
                .validate_checked_invariant_lowerings(&checks, &[])
                .is_err()
        );
        // A body for another judgment cannot certify this bundle.
        let mut incomplete = core.clone();
        Arc::make_mut(incomplete.checked_invariant_lowerings.as_mut().unwrap())
            .body
            .as_mut()
            .unwrap()
            .goal = Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(false), true);
        assert!(
            root(facts.clone(), incomplete)
                .validate_checked_invariant_lowerings(&checks, &[])
                .is_err()
        );
        prepared
            .validate_checked_invariant_lowerings(&checks, &[])
            .unwrap();
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0].saturating_mul(2).saturating_add(8),
            "closure work: {samples:?}"
        );
    }
}
