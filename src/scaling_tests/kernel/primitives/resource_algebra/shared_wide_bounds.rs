#[test]
fn rebased_wide_bounds_retain_cold_coordinate_dags() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::UInt64;
        let base = Pointer {
            block: "wide_bound_scaling".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let mut root = KernelTerm::variable(KernelType::Program(ty.c_type()), Variable(1018502));
        for _ in 0..size {
            root =
                KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [root.clone(), root]);
        }
        let index = MachineOperandView::Shared(&root).retain(ty);
        let range = MemoryRange::new_wide(
            Pointer {
                block: base.block.clone(),
                offset: PointerOffsetTerm::Int64Scaled {
                    value: index.clone(),
                    byte_width: 8,
                    unsigned: true,
                },
            },
            MachineTerm::uint64_constant(0),
            MachineTerm::uint64_constant(1),
            8,
        );
        let facts = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let ((first, last), work) = crate::instrumentation::measure_deterministic_work(|| {
            shared_rebased_wide_bounds(&range, &base, &facts).unwrap()
        });
        assert_eq!(first, index);
        let Some((found, op, [left, right])) = last.operand_view().binary() else {
            panic!("shared endpoint addition")
        };
        assert_eq!(found, ty);
        assert_eq!(op, MachineBinaryOp::Add);
        assert_eq!(left.retain(ty), index);
        assert_eq!(right.uint64_constant(), Some(1));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn wide_normalization_candidates_keep_shared_endpoint_keys() {
    let mut costs = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::UInt64;
        let mut root = KernelTerm::variable(KernelType::Program(ty.c_type()), Variable(1081501));
        for _ in 0..size {
            root =
                KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [root.clone(), root]);
        }
        let index = MachineOperandView::Shared(&root).retain(MachineIntegerType::Int64);
        let base = Pointer {
            block: "normalization-shared-index".into(),
            offset: PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Constant(7)),
                Box::new(PointerOffsetTerm::Int64Scaled {
                    value: index.clone(),
                    byte_width: 8,
                    unsigned: true,
                }),
            ),
        };
        let fact = |start, end| {
            ResourceFact::own_memory(MemoryRange::new_wide(
                base.clone(),
                MachineTerm::uint64_constant(start),
                MachineTerm::uint64_constant(end),
                8,
            ))
        };
        let first = fact(0, 1);
        let next = fact(1, 2);
        let gap = fact(3, 4);
        let facts = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut index = ResourceNormalizationIndex::default();
            index.insert(1, &next);
            index.insert(2, &gap);
            assert_eq!(index.candidates_after(0, &first, &facts), vec![1]);
            index.remove(1, &next);
            assert!(index.candidates_after(0, &first, &facts).is_empty());
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(!index.has_boxed_operand());
        costs.push(work);
    }
    assert!(costs[1] <= costs[0] * 5 + 100, "{costs:?}");
    assert!(costs[2] <= costs[1] * 5 + 100, "{costs:?}");
}
