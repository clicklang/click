use super::*;

#[test]
fn signedness_casts_retain_growing_prefixes_without_exports() {
    for (signed, unsigned) in PAIRS {
        let mut previous = None;
        for size in [16, 64, 256] {
            let _session = VerificationSession::enter();
            let mut root = KernelTermImport::default()
                .machine(signed, &MachineTerm::Variable(Variable(995425)));
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..size {
                    root = shared_machine::cast_signedness(
                        &SpecValue::Shared(root.clone()),
                        unsigned.c_type(),
                    )
                    .unwrap();
                    root = shared_machine::cast_signedness(
                        &SpecValue::Shared(root.clone()),
                        signed.c_type(),
                    )
                    .unwrap();
                    let one =
                        crate::kernel::machine_integer::range::constant_word(signed, &1.into())
                            .unwrap();
                    root = KernelTerm::machine_binary_shared(
                        signed,
                        MachineBinaryOp::Add,
                        [
                            root.clone(),
                            KernelTermImport::default().machine(signed, &one),
                        ],
                    );
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            if let Some(before) = previous {
                assert!(
                    work <= before * 5 + 8,
                    "{signed:?}: {size}: {work} vs {before}"
                );
            }
            previous = Some(work);
        }
    }
}

#[test]
fn opaque_signedness_cast_chains_keep_shared_parents() {
    for (signed, unsigned) in PAIRS {
        let mut previous = None;
        for size in [16, 64, 256] {
            let _session = VerificationSession::enter();
            let leaf = MachineTerm::opaque_conversion(
                "opaque_cast_scaling",
                MachineTerm::Variable(Variable(995426)),
            );
            let mut root = KernelTerm::retained_native_machine_operand(signed, &leaf);
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..size {
                    root = shared_machine::cast_signedness(
                        &SpecValue::Shared(root),
                        unsigned.c_type(),
                    )
                    .unwrap();
                    assert!(!matches!(root.node(), KernelTermNode::Legacy(_)));
                    root =
                        shared_machine::cast_signedness(&SpecValue::Shared(root), signed.c_type())
                            .unwrap();
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            if let Some(before) = previous {
                assert!(
                    work <= before * 5 + 8,
                    "{signed:?}: {size}: {work} vs {before}"
                );
            }
            previous = Some(work);
        }
    }
}
