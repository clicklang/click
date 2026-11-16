use crate::kernel::{KernelTerm, KernelTermExport, KernelType, MachineBinaryOp};
use crate::kernel::machine_integer::comparison::condition_for_operand_views;

#[test]
fn signed_range_admission_ignores_unrelated_facts() {
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut parent = PureFactContext::new();
        for id in 0..size {
            parent = parent.assume_condition(ConditionTerm::equal(
                MachineTerm::Variable(Variable(740_000 + id)), MachineTerm::constant(7)), true);
        }
        let x = MachineTerm::Variable(Variable(750_000));
        let query = ConditionTerm::unsigned_less_equal(x.clone(), MachineTerm::constant(256));
        let expected = Proposition::ConditionIs(ConditionTerm::signed_less_equal(
            MachineTerm::constant(0), signed_uint32_term(x)), true);
        let (child, work) = crate::instrumentation::measure_deterministic_work(|| {
            parent.clone().assume_condition(query, true)
        });
        assert!(child.contains_assumed_exact(&expected));
        assert!(!parent.contains_assumed_exact(&expected));
        samples.push(work);
    }
    assert!(*samples.iter().max().unwrap() <= samples[0] * 4 + 200, "{samples:?}");
}

#[test]
fn signed_range_decision_retains_shared_operands_without_history_or_exports() {
    for hit in [false, true] {
        let mut samples = Vec::new();
        for size in [16, 64, 256, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut root = KernelTerm::variable(
                KernelType::Program(crate::kernel::ProgramType::UInt32), Variable(760_000));
            let mut facts = PureFactContext::new();
            for id in 0..size {
                root = KernelTerm::machine_binary_shared(MachineIntegerType::UInt32,
                    MachineBinaryOp::Multiply, [root.clone(), root]);
                facts = facts.assume_condition(ConditionTerm::equal(
                    MachineTerm::Variable(Variable(770_000 + id)), MachineTerm::constant(7)), true);
            }
            let source = MachineOperandView::Shared(&root).retain(MachineIntegerType::UInt32);
            let signed = source.checking_cast_operand(MachineIntegerType::Int32);
            let zero = MachineTerm::constant(0);
            let maximum = MachineTerm::constant(256);
            facts = facts.assume_condition(condition_for_operand_views(
                MachineIntegerType::Int32, CompareRelation::LessEqual,
                [MachineOperandView::Legacy(&zero), signed.operand_view()]), true);
            if hit {
                facts = facts.assume_condition(condition_for_operand_views(
                    MachineIntegerType::Int32, CompareRelation::LessEqual,
                    [signed.operand_view(), MachineOperandView::Legacy(&maximum)]), true);
            }
            let query = condition_for_operand_views(MachineIntegerType::UInt32,
                CompareRelation::LessEqual, [source.operand_view(), MachineOperandView::Legacy(&maximum)]);
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..3 {
                    assert_eq!(facts.decide_unsigned_small_bound(&query), if hit {Some(true)} else {None});
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            samples.push(work);
        }
        assert!(*samples.iter().max().unwrap() <= samples[0] * 4 + 200,
            "hit={hit}, work={samples:?}");
    }
}
