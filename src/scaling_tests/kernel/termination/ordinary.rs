use super::*;

#[test]
fn selected_termination_steps_do_not_visit_unrelated_functions_or_goals() {
    for size in [1, 16, 64, 256, 1024] {
        let scope = scope(size);
        let proof = Proof::for_program_termination((), scope.clone(), ());
        let ((proof, work), index_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let proof = proof
                    .check_termination(&TerminationCheck::Local("leaf0".into()))
                    .unwrap()
                    .0;
                proof
                    .check_termination(&TerminationCheck::Component {
                        function: "leaf0".into(),
                        strict: false,
                    })
                    .unwrap()
                    .0
            })
        });
        assert!(work <= 16, "{size} functions: {work} check work");
        assert!(
            index_work <= 512,
            "{size} functions: {index_work} persistent work"
        );
        let goal = scope.atom(TerminationAtomKind::Returns, "leaf0").unwrap();
        let (plan, work) = crate::instrumentation::measure_deterministic_work(|| {
            scope.plan(&goal, &ProofFacts::default()).unwrap()
        });
        assert_eq!(plan.len(), 2);
        assert!(work <= 16, "{size} functions: {work} plan work");
        assert!(proof.finish_program_termination().is_err());
    }
}

#[test]
fn whole_termination_proof_and_completion_scale_with_explicit_output() {
    for size in [1, 16, 64, 256, 512] {
        let scope = scope(size);
        let proof = Proof::for_program_termination((), scope.clone(), ());
        let ((proof, work), index_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let mut proof = proof;
                for step in scope.plan(scope.goal(), &ProofFacts::default()).unwrap() {
                    proof = proof.check_termination(&step).unwrap().0;
                }
                proof
                    .apply_known(PropositionKnownContext::Exact)
                    .unwrap_or_else(|_| panic!("checked termination facts close the root"))
            })
        });
        assert!(work <= 128 * size + 128, "{size}: {work} proof work");
        assert!(
            index_work <= 512 * size * (size + 2).ilog2() as usize + 512,
            "{size}: {index_work} persistent work"
        );
        let proved = proof.finish_program_termination().unwrap();
        let ((completed, work), index_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| proved.complete())
        });
        assert_eq!(
            (work, index_work),
            (0, 0),
            "completion only moves the proved program"
        );
        assert_eq!(completed.into_termination_rules().len(), size);
    }
}

#[test]
fn termination_dependency_planning_stops_at_the_ordinary_run_budget() {
    for size in [16, 64, 256] {
        let scope = scope(size);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::instrumentation::with_run_work_limit(8, || {
                scope.plan(scope.goal(), &ProofFacts::default())
            })
        });
        assert!(result.unwrap_err().contains("solve budget"));
        assert!(
            work <= 10,
            "{size} functions: {work} work before bounded refusal"
        );
    }
}
