use super::*;

#[test]
fn widening_casts_retain_growing_arithmetic_prefixes_without_exports() {
    for source in FORMATS {
        for destination in FORMATS {
            if source.format().bits() >= destination.format().bits() {
                continue;
            }
            let mut previous = None;
            for size in [16, 64, 256] {
                let _session = VerificationSession::enter();
                let mut root = KernelTermImport::default()
                    .machine(source, &MachineTerm::Variable(Variable(995432)));
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
                        let cast = shared_machine::cast_widening(
                            &SpecValue::Shared(root.clone()),
                            destination.c_type(),
                        )
                        .unwrap();
                        assert_eq!(cast.children()[0], root);
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
