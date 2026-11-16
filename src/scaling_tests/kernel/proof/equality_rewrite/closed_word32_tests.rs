// Deterministic scaling of checked equality rewriting of closed word arithmetic.
use super::*;

#[test]
fn newly_closed_word32_rewrite_visits_each_shared_node_once() {
    for format in [MachineIntegerType::Int32, MachineIntegerType::UInt32] {
        let mut samples = Vec::new();
        for depth in [8usize, 32, 128, 512] {
            let _session = VerificationSession::enter();
            let variable = MachineTerm::Variable(Variable(992595));
            let replacement =
                crate::kernel::machine_integer::range::constant_word(format, &9.into()).unwrap();
            let mut root = KernelTermImport::default()
                .machine_arithmetic(format, &variable)
                .unwrap();
            for _ in 0..depth {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Divide,
                    [root.clone(), root.clone()],
                );
            }
            let goal = Proposition::ConditionIs(
                ConditionTerm::IntegerLessEqual(
                    IntegerTerm::Machine(
                        SharedMachineIntegerTerm::from_shared(format, root).unwrap(),
                    )
                    .into(),
                    IntegerTerm::constant_i64(5).into(),
                ),
                true,
            );
            let equality = Proposition::ConditionIs(
                ConditionTerm::machine_compare(
                    format,
                    CompareRelation::Equal,
                    variable.clone(),
                    replacement,
                ),
                true,
            );
            let facts = ProofFacts::from_ordered(std::slice::from_ref(&equality));
            let exports = KernelTermExport::machine_export_count();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.check_equality_rewrite(&goal, &equality).unwrap()
            });
            assert_eq!(
                result.proposition(),
                &Proposition::ConditionIs(
                    ConditionTerm::IntegerLessEqual(
                        IntegerTerm::constant_i64(1).into(),
                        IntegerTerm::constant_i64(5).into(),
                    ),
                    true
                )
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            samples.push(work);
        }
        assert!(samples.iter().all(|work| *work > 0));
        for pair in samples.windows(2) {
            assert!(pair[1] <= pair[0] * 4 + 64, "{format:?}: {samples:?}");
        }
    }
}

#[test]
fn newly_closed_word32_rewrite_ignores_unrelated_facts() {
    use crate::kernel::proof::ProofFacts;
    for format in [MachineIntegerType::Int32, MachineIntegerType::UInt32] {
        let mut baseline = None;
        for unrelated in [0usize, 16, 64, 256] {
            let _session = VerificationSession::enter();
            let variable = MachineTerm::Variable(Variable(992596));
            let word = |n: i64| {
                crate::kernel::machine_integer::range::constant_word(format, &n.into()).unwrap()
            };
            let equality = Proposition::ConditionIs(
                ConditionTerm::machine_compare(
                    format,
                    CompareRelation::Equal,
                    variable.clone(),
                    word(9),
                ),
                true,
            );
            let mut premises = vec![equality.clone()];
            premises.extend((0..unrelated).map(|i| Proposition::Predicate {
                name: format!("unused_{i}"),
                arguments: vec![],
            }));
            let facts = ProofFacts::from_ordered(&premises);
            let root = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Divide,
                [
                    KernelTermImport::default()
                        .machine_arithmetic(format, &variable)
                        .unwrap(),
                    KernelTermImport::default()
                        .machine_arithmetic(format, &word(3))
                        .unwrap(),
                ],
            );
            let goal = Proposition::ConditionIs(
                ConditionTerm::IntegerLessEqual(
                    IntegerTerm::Machine(
                        SharedMachineIntegerTerm::from_shared(format, root).unwrap(),
                    )
                    .into(),
                    IntegerTerm::constant_i64(5).into(),
                ),
                true,
            );
            let exports = KernelTermExport::machine_export_count();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.check_equality_rewrite(&goal, &equality).unwrap()
            });
            assert_eq!(
                result.proposition(),
                &Proposition::ConditionIs(
                    ConditionTerm::IntegerLessEqual(
                        IntegerTerm::constant_i64(3).into(),
                        IntegerTerm::constant_i64(5).into(),
                    ),
                    true
                )
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(work > 0);
            let expected = *baseline.get_or_insert(work);
            assert!(
                work <= expected * 2,
                "{format:?}, unrelated={unrelated}: {work} vs {expected}"
            );
        }
    }
}
