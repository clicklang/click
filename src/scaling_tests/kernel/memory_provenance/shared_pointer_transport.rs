use super::*;

#[test]
fn shared_pointer_transport_walks_offset_dags_once_beside_unrelated_state() {
    for unrelated in [0, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let (before, field, other) = tests::fixture();
        let mut context = PureFactContext::new();
        for i in 0..unrelated {
            context = context.assume_condition(
                ConditionTerm::equal(
                    MachineTerm::Variable(Variable(1008000 + i)),
                    MachineTerm::constant(1),
                ),
                true,
            );
        }
        let after = before
            .memory()
            .clone()
            .store(other, ProgramValue::Int32(MachineTerm::constant(3)));
        for size in [16, 64, 256] {
            let index = KernelTermImport::default().machine(
                MachineIntegerType::Int32,
                &MachineTerm::MemoryLoad(before.clone(), Box::new(field.clone()), LoadKind::Int32),
            );
            let mut offset = KernelPointerOffset::Int32Scaled {
                value: index,
                byte_width: 4,
            }
            .into_shared()
            .unwrap();
            for _ in 0..size {
                offset = KernelPointerOffset::Add([offset.clone(), offset])
                    .into_shared()
                    .unwrap();
            }
            let source = SharedPointerAddress::new(
                SharedPointerBlock::import(&PointerBlock::Symbolic(Variable(1009000))),
                offset,
            );
            let exports = KernelTermExport::machine_export_count();
            let (output, work) = crate::instrumentation::measure_deterministic_work(|| {
                transport_address(&source, &after, Some((&context, true))).unwrap()
            });
            assert!(matches!(
                output.node().offset.node(),
                KernelPointerOffset::Add(_)
            ));
            assert!(
                work <= 50 * size + 2000,
                "size={size}, unrelated={unrelated}, work={work}"
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
}
