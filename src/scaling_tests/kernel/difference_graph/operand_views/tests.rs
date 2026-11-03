use super::*;
use crate::kernel::{KernelTerm, KernelType};
#[test]
fn graph_overflow_queries_visit_shared_dag_nodes_once() {
    let mut samples = Vec::new();
    for size in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let variable = Variable(997831);
        let mut root = KernelTerm::variable(KernelType::C(ty.c_type()), variable);
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                ty,
                MachineBinaryOp::Add,
                [root.clone(), root.clone()],
            );
        }
        let operand = SharedMachineIntegerTerm::from_shared(ty, root).unwrap();
        let zero = Bitvector32Term::Constant(0);
        let query = OverflowQueryView::from_operands(
            ty,
            Op::Add,
            [operand.operand_view(), V::Legacy(&zero)],
        )
        .unwrap();
        let mut graph = DifferenceGraph::new();
        graph.assume_condition(
            &ConditionTerm::equal(Bitvector32Term::Variable(variable), zero),
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
