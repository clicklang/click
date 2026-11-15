#[test]
fn retiring_one_program_goal_does_not_visit_sibling_obligations() {
    for siblings in [0_usize, 16, 64, 256, 1024] {
        let requested = (0..siblings)
            .map(|index| format!("sibling{index}"))
            .chain(["selected".into()])
            .collect();
        let root = ProgramContractProof::open(requested, BTreeSet::new(), &BTreeSet::new());
        let mut guard = root.bodies.0.lock().unwrap();
        let root = guard.as_mut().unwrap();
        let (((), work), index_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                root.retire(&ProgramContractGoal::Returns("selected".into()));
            })
        });
        assert_eq!(root.open.len(), siblings + 2);
        assert!(work <= 16, "{siblings} siblings: {work} work");
        assert!(
            index_work <= 64 * (siblings + 2).ilog2() as usize + 64,
            "{siblings} siblings: {index_work} index work"
        );
        assert!(
            root.proof.completion().is_none(),
            "callback safety remains open"
        );
    }
}

#[test]
fn opening_one_body_does_not_visit_previously_opened_bodies() {
    for siblings in [0_usize, 16, 64, 256, 1024] {
        let root = ProgramContractProof::open(BTreeSet::new(), BTreeSet::new(), &BTreeSet::new());
        let bodies = root.bodies();
        for index in 0..siblings {
            bodies.open_body(format!("sibling{index}"));
        }
        let ((_, work), index_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                bodies.open_body("selected".into())
            })
        });
        assert!(work <= 16, "{siblings} prior bodies: {work} work");
        assert!(
            index_work <= 128 * (siblings + 2).ilog2() as usize + 128,
            "{siblings} prior bodies: {index_work} index work"
        );
        let state = bodies.0.lock().unwrap();
        assert_eq!(state.as_ref().unwrap().pending_bodies.len(), siblings + 1);
    }
}

#[test]
fn generation_and_execution_scale_with_requirements_and_completion_only_moves_the_proof() {
    for size in [16_usize, 64, 256, 512] {
        let rules = (0..size)
            .map(|index| tests::rule(&format!("leaf{index}"), ProgramStatement::Skip))
            .collect::<Vec<_>>();
        let requested = rules
            .iter()
            .map(|rule| rule.function.name().to_string())
            .collect();
        let root = ProgramContractProof::open(requested, BTreeSet::new(), &BTreeSet::new());
        let (proof, generation_work) = crate::instrumentation::measure_deterministic_work(|| {
            root.generate_termination(ProgramTerminationInputs {
                partial_rules: &rules,
                plans: &[],
                inline_bodies: &[],
                assumed_terminating: &BTreeSet::new(),
                diverging_contracts: &BTreeSet::new(),
                has_unselected_functions: false,
            })
            .unwrap_or_else(|_| panic!("generate leaf return requirements"))
        });
        assert!(proof.state.proof.completion().is_none());
        assert_eq!(proof.obligations.function_goals.len(), size);
        assert!(
            generation_work <= 64 * size + 64,
            "{size} requirements: {generation_work} generation work"
        );
        let (proved, execution_work) = crate::instrumentation::measure_deterministic_work(|| {
            proof
                .prove_implicitly()
                .unwrap_or_else(|_| panic!("prove leaf requirements"))
        });
        assert!(proved.proof.completion().is_some());
        assert!(
            execution_work <= 64 * size + 64,
            "{size} requirements: {execution_work} execution work"
        );
        let ((completed, completion_work), index_work) =
            crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| proved.complete())
            });
        assert_eq!(completion_work, 0, "completion must not execute a checker");
        assert_eq!(
            index_work, 0,
            "completion must not inspect the proof's indexes"
        );
        assert_eq!(completed.into_termination_rules().len(), size);
    }
}
