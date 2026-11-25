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

#[test]
fn completion_compares_shared_conditional_words_without_export() {
    use crate::kernel::{KernelTermExport, KernelType, MachineBinaryOp};
    for depth in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let guard =
            KernelTermImport::default().condition(&ConditionTerm::Variable(Variable(100_299)));
        let leaf = KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(100_300));
        let mut word = leaf.clone();
        for _ in 0..depth {
            word = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [word.clone(), word],
            );
        }
        let left =
            KernelTerm::machine_if_shared(format, [guard.clone(), word.clone(), word.clone()]);
        let right = KernelTerm::machine_if_shared(
            MachineIntegerType::UInt32,
            [guard.clone(), word.clone(), word.clone()],
        );
        assert_ne!(left, right);
        let different = KernelTerm::machine_if_shared(format, [guard, word, leaf]);
        for (right, expected) in [(right, true), (different, false)] {
            let condition = KernelTerm::boolean_comparison_raw(
                format,
                CompareRelation::Equal,
                [left.clone(), right],
            );
            let exports = KernelTermExport::machine_export_count();
            let (reflexive, work) = crate::instrumentation::measure_deterministic_work(|| {
                reflexive_completion_condition(BooleanOperandView::Shared(&condition))
            });
            assert_eq!(reflexive, expected);
            assert!(work <= 4 * depth + 20, "depth={depth}, work={work}");
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(!condition.has_cached_native_argument());
        }
    }
}
