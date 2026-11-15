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
