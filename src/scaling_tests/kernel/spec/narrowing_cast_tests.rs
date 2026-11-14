use super::*;

#[test]
fn narrowing_casts_retain_growing_arithmetic_prefixes_without_exports() {
    for source in FORMATS {
        for destination in FORMATS {
            if source.format().bits() <= destination.format().bits() {
                continue;
            }
            let mut previous = None;
            for size in [16, 64, 256] {
                let _session = VerificationSession::enter();
                let mut root = KernelTermImport::default()
                    .machine(source, &MachineTerm::Variable(Variable(995442)));
                let one = crate::kernel::machine_integer::range::constant_word(source, &1.into())
                    .unwrap();
                let one = KernelTermImport::default().machine(source, &one);
                let exports = KernelTermExport::machine_export_count();
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    for _ in 0..size {
                        root = KernelTerm::machine_binary_shared(
                            source,
                            MachineBinaryOp::Add,
                            [root.clone(), one.clone()],
                        );
                        let cast = shared_machine::cast_narrowing(
                            &SpecValue::Shared(root.clone()),
                            destination.program_type(),
                        )
                        .unwrap();
                        assert!(cast.is_shared_machine_operand());
                        assert_eq!(cast.ty(), &KernelType::Program(destination.program_type()));
                    }
                });
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                if let Some(before) = previous {
                    assert!(
                        work <= before * 5 + 8,
                        "{source:?}->{destination:?}: {size}: {work} vs {before}"
                    );
                }
                previous = Some(work);
            }
        }
    }
}
