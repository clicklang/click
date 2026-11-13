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
            index.adjust(&equality, true);
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

#[test]
fn common_call_sources_preserve_identity_polarity_and_branch_authority() {
    use crate::kernel::machine_integer::comparison::condition_for_operand_views;
    use crate::kernel::{
        KernelTermExport, KernelTermImport, MachineOperandView as V, SharedPureApplication,
    };
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let _session = crate::kernel::VerificationSession::enter();
        let application = SharedPureApplication::intern("fact_call".into(), vec![]);
        let root = KernelTermImport::default().machine_call(format, &application);
        let native = MachineTerm::ClickFunctionApplication {
            name: "fact_call".into(),
            arguments: vec![],
        };
        let bound =
            crate::kernel::machine_integer::range::constant_word(format, &7.into()).unwrap();
        for relation in [CompareRelation::Equal, CompareRelation::LessThan] {
            let written =
                ConditionTerm::machine_compare(format, relation, native.clone(), bound.clone());
            let shared = condition_for_operand_views(
                format,
                relation,
                [V::Shared(&root), V::Legacy(&bound)],
            );
            for (source, query) in [(&written, &shared), (&shared, &written)] {
                for truth in [false, true] {
                    let parent = PureFactContext::new();
                    let child = parent.clone().assume_condition(source.clone(), truth);
                    let exports = KernelTermExport::machine_export_count();
                    assert_eq!(
                        child.selected_comparison_source(query, truth),
                        Some(&Proposition::ConditionIs(source.clone(), truth))
                    );
                    assert!(child.selected_comparison_source(query, !truth).is_none());
                    assert!(parent.selected_comparison_source(query, truth).is_none());
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                }
            }
        }
    }
}

#[test]
fn common_call_fact_queries_do_not_scan_growing_source_buckets() {
    use crate::kernel::machine_integer::comparison::condition_for_operand_views;
    use crate::kernel::{
        KernelTermExport, KernelTermImport, MachineOperandView as V, SharedPureApplication,
    };
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let application = SharedPureApplication::intern("indexed_call".into(), vec![]);
        let root = KernelTermImport::default().machine_call(format, &application);
        let native = MachineTerm::ClickFunctionApplication {
            name: "indexed_call".into(),
            arguments: vec![],
        };
        let mut context = PureFactContext::new();
        for n in 1..=size {
            context = context.assume_condition(
                ConditionTerm::signed_less_than(native.clone(), MachineTerm::constant(n)),
                true,
            );
            context = context.assume_condition(
                ConditionTerm::signed_less_than(
                    MachineTerm::Variable(Variable(995840 + n as u64)),
                    MachineTerm::constant(n),
                ),
                true,
            );
        }
        let bound = MachineTerm::constant(1);
        let query = condition_for_operand_views(
            format,
            CompareRelation::LessThan,
            [V::Shared(&root), V::Legacy(&bound)],
        );
        assert!(context.selected_comparison_source(&query, true).is_some());
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(context.selected_comparison_source(&query, true).is_some());
            assert!(context.selected_comparison_source(&query, false).is_none());
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 16),
        "{samples:?}"
    );
}
