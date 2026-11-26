use super::*;

#[test]
fn pointer_relevance_visits_shared_prefixes_once() {
    use crate::kernel::{
        AddressBase, KernelTerm, KernelTermExport, KernelType, MachineOperandView as View,
        OldAddress, OldAddressOffset, Variable,
    };
    let target = OldAddress {
        base: AddressBase::Concrete("unrelated".into()),
        offset: OldAddressOffset::Constant(0).into(),
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
        let proposition = Proposition::condition_is(condition, true);
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
