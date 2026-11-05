#[test]
fn conservative_carrier_queries_do_not_rewalk_growing_prefixes() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256] {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut root = KernelTerm::variable(KernelType::C(CType::Int32), Variable(998100));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [
                        root.clone(),
                        KernelTerm::variable(KernelType::C(CType::Int32), Variable(998101 + index)),
                    ],
                );
                let term = IntegerTerm::Machine(
                    SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap(),
                );
                assert!(integer_carrier_in_integer(&term, Variable(998999)));
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{samples:?}");
    }
}

#[test]
fn fold_item_domains_retain_growing_endpoints_at_each_width() {
    use crate::kernel::machine_integer::{Relation, comparison::structural_native_comparison_view};
    for format in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
        let mut samples = Vec::new();
        for size in [16u64, 64, 256] {
            let _session = VerificationSession::enter();
            let item = Variable(1003000);
            let mut root = KernelTerm::variable(KernelType::C(format.c_type()), Variable(1003001));
            let seed = SharedIntegerRangeEndpoint::intern(MachineTerm::constant(0));
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for index in 0..size {
                    root = KernelTerm::machine_binary_shared(
                        format,
                        MachineBinaryOp::Add,
                        [
                            root.clone(),
                            KernelTerm::variable(
                                KernelType::C(format.c_type()),
                                Variable(1003002 + index),
                            ),
                        ],
                    );
                    let endpoint = seed
                        .with_shared_operand(
                            root.with_machine_observation_type(MachineIntegerType::Int32),
                        )
                        .unwrap();
                    let index = match format {
                        MachineIntegerType::Int32 => IntegerRangeFoldIndex::Int32 {
                            start: endpoint.clone(),
                            end: endpoint,
                        },
                        _ => IntegerRangeFoldIndex::UInt64 {
                            start: endpoint.clone(),
                            end: endpoint,
                        },
                    };
                    let (sort, guard) = integer_range_fold_item_domain(&index, item);
                    assert_eq!(
                        sort,
                        if format == MachineIntegerType::Int32 {
                            Sort::CInt32
                        } else {
                            Sort::CMachineInteger(format)
                        }
                    );
                    let Proposition::And(lower, upper) = guard else {
                        panic!("range guard")
                    };
                    for (part, relation, endpoint_side) in
                        [(lower, Relation::LessEqual, 0), (upper, Relation::Less, 1)]
                    {
                        let Proposition::ConditionIs(condition, true) = *part else {
                            panic!("positive guard")
                        };
                        let view = structural_native_comparison_view(&condition, true).unwrap();
                        assert_eq!(view.format, format);
                        assert_eq!(view.relation, relation);
                        assert_eq!(
                            view.operands[1 - endpoint_side].operand_view().variable(),
                            Some(&item)
                        );
                        assert_eq!(
                            view.operands[endpoint_side]
                                .operand_view()
                                .retain(format)
                                .shared_operand(),
                            Some(&root)
                        );
                    }
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(pair[1] <= pair[0] * 5, "{format:?}: {samples:?}");
        }
    }
}
