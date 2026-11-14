use super::*;

#[test]
fn pointer_readers_visit_shared_offset_and_index_dags_once() {
    for unrelated in [0, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let _unrelated = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(1002000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let source = SharedPointerAddress::import(&Pointer::symbolic(Variable(1003000)));
            let mut index =
                KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(1003001));
            for _ in 0..size {
                index = KernelTerm::machine_binary_shared(
                    MachineIntegerType::Int32,
                    MachineBinaryOp::Add,
                    [index.clone(), index],
                );
            }
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
            let address = SharedPointerAddress::new(source.node().block.clone(), offset);
            let exports = KernelTermExport::machine_export_count();
            let (variables, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut variables = BTreeSet::new();
                collect_address_variables(
                    &address,
                    FoldVariableRead::MachineCapture,
                    &mut variables,
                );
                variables
            });
            assert_eq!(
                variables,
                BTreeSet::from([Variable(1003000), Variable(1003001)])
            );
            assert!(
                work <= 30 * size + 100,
                "size={size}, unrelated={unrelated}, work={work}"
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
}
