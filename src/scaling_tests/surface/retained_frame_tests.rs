use super::*;

#[test]
fn fixed_state_frames_borrow_growing_published_results_without_exports() {
    use crate::kernel::{
        ExecutionValue, KernelTerm, KernelTermExport, KernelType, MachineBinaryOp,
        MachineIntegerType, StoredExecutionValue, Variable,
    };
    let _session = crate::kernel::VerificationSession::enter();
    let state = ExecutionState::new();
    let recorded = RecordedStates::default();
    let mut previous = None;
    for depth in [8, 32, 128] {
        let atom = KernelTerm::variable(KernelType::Program(ProgramType::UInt64), Variable(996920));
        let mut root = atom.clone();
        for _ in 0..depth {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::UInt64,
                MachineBinaryOp::Add,
                [root, atom.clone()],
            );
        }
        let value = StoredExecutionValue::from(ExecutionValue::Shared(root.clone()));
        let exports = KernelTermExport::machine_export_count();
        let (frame, work) = crate::instrumentation::measure_deterministic_work(|| {
            FixedStateFrame::new(&state, &state, None, &recorded).with_retained_result(&value)
        });
        let Some(FixedStateResult::Retained(retained)) = frame.result else {
            panic!("retained frame")
        };
        assert_eq!(retained.shared(), Some(&root));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        if let Some(previous) = previous {
            assert_eq!(work, previous);
        }
        previous = Some(work);
        let native = value.clone().into_native();
        assert_eq!(frame.native_result().as_deref(), Some(&native));
        let legacy = FixedStateFrame::new(&state, &state, Some(&native), &recorded);
        assert!(matches!(
            legacy.native_result(),
            Some(std::borrow::Cow::Borrowed(_))
        ));
    }
}
