use super::*;

#[test]
fn native_order_sources_do_not_add_native_query_work() {
    use crate::kernel::machine_integer::comparison::condition_for_operand_views;
    use crate::kernel::{KernelTermExport, KernelTermImport, MachineOperandView as V};
    for size in [4u64, 32, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut index = ObservationComparisons::default();
        let mut context = PureFactContext::new();
        let bound = MachineTerm::constant(1000);
        let operand_at = |id: u64| MachineTerm::Binary {
            format: MachineIntegerType::Int32,
            op: crate::kernel::MachineBinaryOp::Add,
            left: Box::new(MachineTerm::Variable(Variable(989_200 + id))),
            right: Box::new(MachineTerm::constant(1)),
        };
        for id in 0..size {
            context = context.assume_condition(
                ConditionTerm::signed_less_than(operand_at(id), bound.clone()),
                true,
            );
            index.adjust(
                &ConditionTerm::signed_less_than(operand_at(id), bound.clone()),
                true,
                true,
            );
        }
        let operand = operand_at(0);
        let native = ConditionTerm::signed_less_than(operand.clone(), bound.clone());
        let equality = ConditionTerm::equal(operand.clone(), bound.clone());
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            // Native premises already have their own lookup. This bucket
            // must not add comparison-reading work to those queries.
            assert!(index.source(&native, true).is_none());
            assert!(index.source(&native, false).is_none());
            index.adjust(&equality, true, true);
            index.adjust(&equality, true, false);
        });
        assert_eq!(work, 0, "{size} native order sources");
        let root = KernelTermImport::default()
            .machine_arithmetic(MachineIntegerType::Int32, &operand)
            .unwrap();
        let shared = condition_for_operand_views(
            MachineIntegerType::Int32,
            CompareRelation::LessThan,
            [V::Shared(&root), V::Legacy(&bound)],
        );
        assert_eq!(
            context.selected_comparison_source(&shared, true),
            Some(&Proposition::ConditionIs(native, true))
        );
        assert!(context.selected_comparison_source(&shared, false).is_none());

        let shared_equality = condition_for_operand_views(
            MachineIntegerType::Int32,
            CompareRelation::Equal,
            [V::Shared(&root), V::Legacy(&bound)],
        );
        let without_orders = PureFactContext::new().assume_condition(shared_equality.clone(), true);
        context = context.assume_condition(shared_equality.clone(), true);
        // Warm the syntax identities equally; the only difference is the
        // unrelated native order bucket, which cannot answer equalities.
        assert!(
            without_orders
                .selected_comparison_source(&shared_equality, true)
                .is_some()
        );
        assert!(
            context
                .selected_comparison_source(&shared_equality, true)
                .is_some()
        );
        let (_, baseline) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(
                without_orders
                    .selected_comparison_source(&shared_equality, true)
                    .is_some()
            );
        });
        let (_, alongside_orders) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(
                context
                    .selected_comparison_source(&shared_equality, true)
                    .is_some()
            );
        });
        assert_eq!(
            alongside_orders, baseline,
            "{size} irrelevant native orders"
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}
