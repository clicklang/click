use super::*;

#[test]
fn pointer_relevance_visits_shared_prefixes_once() {
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelType, MachineOperandView as View, Pointer,
        PointerBlock, PointerOffsetTerm, Variable,
    };
    let target = Pointer {
        block: PointerBlock::Concrete("unrelated".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut previous = None;
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt64;
        let mut root =
            KernelTerm::variable(KernelType::Program(format.program_type()), Variable(986320));
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
        }
        let condition = crate::kernel::machine_integer::comparison::condition_for_operand_views(
            format,
            CompareRelation::Equal,
            [View::Shared(&root), View::Shared(&root)],
        );
        let proposition = Proposition::ConditionIs(condition, true);
        let exports = KernelTermExport::machine_export_count();
        let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
            proposition_mentions_pointer(&proposition, &target)
        });
        assert!(!found);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        if let Some(previous) = previous {
            assert!(
                work <= previous * 5,
                "size={size}, work={work}, previous={previous}"
            );
        }
        previous = Some(work);
    }
}
