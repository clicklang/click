use super::*;

#[test]
fn annotated_narrow_chains_retain_operands_without_exports() {
    for format in FORMATS {
        for op in OPS {
            let mut previous = None;
            for size in [16, 64, 256] {
                let _session = VerificationSession::enter();
                let mut root = input(
                    &format.value_from_term(MachineTerm::Variable(Variable(995465))),
                    true,
                );
                let right = root.clone();
                let exports = KernelTermExport::machine_export_count();
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    for _ in 0..size {
                        let result = narrow::apply(format, op, &root, &right).unwrap();
                        let SpecValue::Shared(previous) = root else {
                            panic!()
                        };
                        assert_eq!(result.value.children()[0], previous);
                        root = result.value.into();
                    }
                });
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                if let Some(before) = previous {
                    assert!(
                        work <= before * 5 + 8,
                        "{format:?} {op:?}: {size}: {work} vs {before}"
                    );
                }
                previous = Some(work);
            }
        }
    }
}
