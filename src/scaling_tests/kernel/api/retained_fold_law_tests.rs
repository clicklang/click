#[test]
fn fold_laws_retain_cold_shared_endpoint_dags() {
    for format in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
        let mut samples = Vec::new();
        for depth in [16, 64, 256] {
            let _session = VerificationSession::enter();
            let mut root = KernelTerm::variable(KernelType::C(format.c_type()), Variable(1005100));
            for _ in 0..depth {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [root.clone(), root],
                );
            }
            let zero = if format == MachineIntegerType::Int32 {
                MachineTerm::constant(0)
            } else {
                MachineTerm::uint64_constant(0)
            };
            let start = endpoint(&zero);
            let end = start
                .with_shared_operand(root.with_machine_observation_type(MachineIntegerType::Int32))
                .unwrap();
            let index = match format {
                MachineIntegerType::Int32 => IntegerRangeFoldIndex::Int32 { start, end },
                _ => IntegerRangeFoldIndex::UInt64 { start, end },
            };
            let item = Variable(1005101);
            let accumulator = Variable(1005102);
            let body = IntegerTerm::add(
                IntegerTerm::Variable(accumulator),
                IntegerTerm::from_machine(format, MachineTerm::Variable(item)).unwrap(),
            );
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let empty = prove_integer_range_fold_empty(
                    index.clone(),
                    IntegerTerm::constant_i64(0),
                    accumulator,
                    item,
                    body.clone(),
                );
                assert!(matches!(empty.proposition(), Proposition::Implies(..)));
                let append = prove_integer_range_fold_append(
                    index.clone(),
                    IntegerTerm::constant_i64(0),
                    accumulator,
                    item,
                    body,
                )
                .unwrap();
                assert!(matches!(append.proposition(), Proposition::Implies(..)));
                let (predecessor, _) = integer_range_fold_predecessor_index(&index).unwrap();
                let (original, shifted) = match (&index, predecessor) {
                    (
                        IntegerRangeFoldIndex::Int32 { end, .. },
                        IntegerRangeFoldIndex::Int32 { end: prior, .. },
                    )
                    | (
                        IntegerRangeFoldIndex::UInt64 { end, .. },
                        IntegerRangeFoldIndex::UInt64 { end: prior, .. },
                    ) => (
                        end,
                        shifted_fold_endpoint(&prior, format, MachineBinaryOp::Add),
                    ),
                    _ => panic!("endpoint carrier"),
                };
                assert_eq!(original, &shifted);
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(pair[1] <= pair[0] * 5, "{format:?}: {samples:?}");
        }
    }
}
