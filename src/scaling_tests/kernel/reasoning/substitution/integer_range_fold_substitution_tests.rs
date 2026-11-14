// Retained endpoint dependency collection must follow shared syntax once,
// retaining outer scopes and Integer conversion payloads without expansion.
#[test]
fn bound_variable_collection_keeps_shared_fold_endpoints_and_scopes() {
    use crate::kernel::{KernelTerm, KernelTermExport, KernelTermImport, MachineBinaryOp};
    for format in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
        let mut samples = Vec::new();
        for depth in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let item = Variable(1002000);
            let accumulator = Variable(1002001);
            let converted = Variable(1002002);
            let free_body = Variable(1002003);
            let native = MachineTerm::Binary {
                format,
                op: MachineBinaryOp::Add,
                left: Box::new(MachineTerm::Variable(item)),
                right: Box::new(MachineTerm::IntegerToMachine {
                    value: IntegerTerm::Variable(converted).into(),
                    destination: format,
                }),
            };
            let mut root = KernelTermImport::default()
                .machine_arithmetic(format, &native)
                .unwrap();
            for _ in 0..depth {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [root.clone(), root],
                );
            }
            let zero = match format {
                MachineIntegerType::Int32 => MachineTerm::constant(0),
                _ => MachineTerm::uint64_constant(0),
            };
            let start = SharedIntegerRangeEndpoint::intern(zero);
            // Endpoint storage retains its legacy word observation type; the
            // index variant supplies the endpoint comparison width.
            let root = root.with_machine_observation_type(MachineIntegerType::Int32);
            let end = start.with_shared_operand(root).unwrap();
            let index = match format {
                MachineIntegerType::Int32 => IntegerRangeFoldIndex::Int32 { start, end },
                _ => IntegerRangeFoldIndex::UInt64 { start, end },
            };
            let fold = IntegerTerm::range_fold(
                index,
                IntegerTerm::Variable(accumulator),
                accumulator,
                item,
                IntegerTerm::add(
                    IntegerTerm::Variable(accumulator),
                    IntegerTerm::Variable(free_body),
                ),
            );
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut variables = BTreeSet::new();
                collect_integer_bound_variables(&fold, &mut variables);
                assert_eq!(
                    variables,
                    BTreeSet::from([item, accumulator, converted, free_body])
                );
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(pair[1] <= pair[0] * 5, "{format:?}: {samples:?}");
        }
    }
}

#[test]
fn fold_step_substitution_retains_shared_item_replacements() {
    use crate::kernel::{KernelTerm, KernelTermExport, KernelType, MachineBinaryOp};
    for format in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
        let mut samples = Vec::new();
        for depth in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let item = Variable(1004000);
            let accumulator = Variable(1004001);
            let mut root = KernelTerm::variable(
                KernelType::Program(format.program_type()),
                Variable(1004002),
            );
            for _ in 0..depth {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [root.clone(), root],
                );
            }
            let replacement = IntegerTerm::Machine(
                SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap(),
            );
            let body = IntegerTerm::add(
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    format,
                    MachineTerm::Variable(item),
                )),
                IntegerTerm::Variable(accumulator),
            );
            let exports = KernelTermExport::machine_export_count();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                instantiate_integer_range_fold_step(
                    &body,
                    accumulator,
                    &IntegerTerm::constant_i64(7),
                    item,
                    &replacement,
                    Some(format),
                )
                .unwrap()
            });
            let IntegerTerm::Add(left, right) = result else {
                panic!("fold step addition")
            };
            let IntegerTerm::Machine(value) = left.as_ref() else {
                panic!("retained item")
            };
            assert_eq!(value.shared_operand(), Some(&root));
            assert_eq!(right.as_ref(), &IntegerTerm::constant_i64(7));
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(pair[1] <= pair[0] * 5, "{format:?}: {samples:?}");
        }
    }
}
