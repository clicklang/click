use super::*;

#[test]
fn match_alpha_identity_work_scales_with_selected_arms() {
    let samples = [16, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let left = selected_match(100, size);
        let right = selected_match(200, size);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(key(&left), key(&right));
        });
        (size, work)
    });
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(*sw > 0);
        assert!(lw * small <= sw * large * 2, "{samples:?}");
    }
}

#[test]
fn common_match_alpha_identity_keeps_shared_arm_body() {
    use crate::kernel::{
        KernelMatch, KernelTerm, KernelTermExport, KernelTermImport, KernelType, MachineBinaryOp,
        MachineIntegerType,
    };
    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut left = KernelMatch::import_machine(
            &mut KernelTermImport::default(),
            MachineIntegerType::Int32,
            &selected_match(100, 1),
        )
        .unwrap();
        let mut right = KernelMatch::import_machine(
            &mut KernelTermImport::default(),
            MachineIntegerType::Int32,
            &selected_match(200, 1),
        )
        .unwrap();
        for (matched, id) in [(&mut left, 100), (&mut right, 200)] {
            let mut body = KernelTerm::variable(KernelType::C(ProgramType::Int32), Variable(id));
            for _ in 0..size {
                body = KernelTerm::machine_binary_shared(
                    MachineIntegerType::Int32,
                    MachineBinaryOp::Add,
                    [body.clone(), body],
                );
            }
            matched.arguments[1] = body;
        }
        let exports = KernelTermExport::machine_export_count();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            retained_alpha_equivalent(&left, &right)
        });
        assert_eq!(result, Some(true));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work <= 100 * size + 100, "size={size}, work={work}");
    }
}
