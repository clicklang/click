use super::*;

#[test]
fn pointer_rewrites_visit_shared_offset_dags_once_and_reuse_numeric_results() {
    struct Replace {
        from: KernelTerm,
        to: KernelTerm,
        calls: usize,
    }
    impl PointerRewrite for Replace {
        type Error = ();
        fn numeric(&mut self, value: &KernelTerm) -> Result<KernelTerm, ()> {
            self.calls += 1;
            Ok(if value == &self.from {
                self.to.clone()
            } else {
                value.clone()
            })
        }
    }
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(1005000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let source = SharedPointerAddress::import(&Pointer::symbolic(Variable(1006000)));
            let from =
                KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(1006001));
            let to =
                KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(1006002));
            let mut offset = KernelPointerOffset::Int32Scaled {
                value: from.clone(),
                byte_width: 4,
            }
            .into_shared()
            .unwrap();
            for _ in 0..size {
                offset = KernelPointerOffset::Add([offset.clone(), offset])
                    .into_shared()
                    .unwrap();
            }
            let source = SharedPointerAddress::new(source.node().block.clone(), offset);
            let mut selected = Replace { from, to, calls: 0 };
            let exports = KernelTermExport::machine_export_count();
            let (output, work) = crate::instrumentation::measure_deterministic_work(|| {
                source.try_rewrite(&mut selected).unwrap()
            });
            assert_ne!(output, source);
            assert_eq!(selected.calls, 1);
            assert!(
                work <= 14 * size + 40,
                "size={size}, unrelated={unrelated}, work={work}"
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
}
