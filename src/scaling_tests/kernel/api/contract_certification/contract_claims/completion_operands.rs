#[test]
fn completion_skips_nonreflexive_connective_dags() {
    let _session = crate::kernel::VerificationSession::enter();
    let leaf = KernelTermImport::default().condition(&ConditionTerm::Variable(Variable(100_298)));
    for depth in [4, 8, 12, 16] {
        let mut root = leaf.clone();
        for _ in 0..depth {
            root = KernelTerm::boolean_equal_raw([root.clone(), root]);
        }
        let goal =
            Proposition::ConditionIs(StoredConditionTerm::from_root(root.clone()).unwrap(), true);
        let (key, work) =
            crate::instrumentation::measure_deterministic_work(|| completion_key(&goal));
        assert!(work <= 4, "depth={depth}, work={work}");
        let Proposition::ConditionIs(condition, true) = key else {
            panic!("Boolean equality keeps its original certification rule");
        };
        assert_eq!(condition.root(), Some(&root));
        assert!(!root.has_cached_native_argument());
    }
}
