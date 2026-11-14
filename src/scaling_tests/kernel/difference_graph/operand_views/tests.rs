use super::*;
use crate::kernel::{KernelTerm, KernelType};
#[test]
fn graph_overflow_queries_visit_shared_dag_nodes_once() {
    let mut samples = Vec::new();
    for size in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let variable = Variable(997831);
        let mut root = KernelTerm::variable(KernelType::Program(ty.program_type()), variable);
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                ty,
                MachineBinaryOp::Add,
                [root.clone(), root.clone()],
            );
        }
        let operand = SharedMachineIntegerTerm::from_shared(ty, root).unwrap();
        let zero = MachineTerm::constant(0);
        let query = OverflowQueryView::from_operands(
            ty,
            Op::Add,
            [operand.operand_view(), V::Legacy(&zero)],
        )
        .unwrap();
        let mut graph = DifferenceGraph::new();
        graph.assume_condition(
            &ConditionTerm::equal(MachineTerm::Variable(variable), zero),
            true,
        );
        let before = KernelTermExport::machine_export_count();
        let (answer, work) = crate::instrumentation::measure_deterministic_work(|| {
            graph.decide_overflow_query(&query)
        });
        assert_eq!(answer, Some(false));
        assert_eq!(KernelTermExport::machine_export_count(), before);
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small * 4 <= sw * large * 5, "{samples:?}");
    }
}

#[test]
fn graph_queries_reuse_prefixes_across_unrelated_fact_additions() {
    check_changing_context_prefixes(false);
    check_changing_context_prefixes(true);
}

fn check_changing_context_prefixes(bounded: bool) {
    use crate::kernel::machine_integer::Relation;
    use crate::kernel::machine_integer::comparison::{ComparisonOperand, NativeComparisonView};
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let mut root =
            KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(998301));
        let zero = KernelTermImport::default()
            .machine_arithmetic(ty, &0u32.into())
            .unwrap();
        let mut graph = DifferenceGraph::new();
        if bounded {
            let base = MachineTerm::Variable(Variable(998301));
            graph.assume_condition(
                &ConditionTerm::signed_less_equal(0u32.into(), base.clone()),
                true,
            );
            graph.assume_condition(&ConditionTerm::signed_less_equal(base, 10u32.into()), true);
        }
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for i in 0..size {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [root.clone(), zero.clone()],
                );
                graph.assume_condition(
                    &ConditionTerm::equal(
                        MachineTerm::Variable(Variable(998400 + i as u64)),
                        (i as u32).into(),
                    ),
                    true,
                );
                let query = NativeComparisonView {
                    format: ty,
                    relation: Relation::LessEqual,
                    operands: [
                        ComparisonOperand::Observation(
                            SharedMachineIntegerTerm::from_shared(ty, root.clone()).unwrap(),
                        ),
                        ComparisonOperand::Constant(10u32.into()),
                    ],
                };
                assert_eq!(graph.decide_shared_order(&query), bounded.then_some(true));
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 5 + 100, "{samples:?}");
    }
}

#[test]
fn growing_shared_order_sources_are_indexed_without_exporting_prefixes() {
    use crate::kernel::machine_integer::comparison::{
        comparison_view, condition_for_operand_views,
    };
    let mut samples = Vec::new();
    for size in [32, 64, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let mut root =
            KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(998701));
        let one = KernelTermImport::default()
            .machine_arithmetic(ty, &1u32.into())
            .unwrap();
        let upper = KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(998702));
        let mut graph = DifferenceGraph::new();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [root.clone(), one.clone()],
                );
                let source = condition_for_operand_views(
                    ty,
                    CompareRelation::LessThan,
                    [V::Shared(&root), V::Shared(&upper)],
                );
                graph.assume_condition(&source, true);
                assert_eq!(
                    graph.decide_shared_order(&comparison_view(&source, true).unwrap()),
                    Some(true)
                );
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 3 + 100, "{samples:?}");
    }
}
