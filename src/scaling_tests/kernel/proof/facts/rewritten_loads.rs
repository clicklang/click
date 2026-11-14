#[test]
fn retained_rewritten_loads_share_syntax_but_recheck_authority() {
    for conditional in [false, true] {
        for prefixes in [false, true] {
            let mut samples = Vec::new();
            for size in [16, 64, 256] {
                let _session = VerificationSession::enter();
                let format = MachineIntegerType::Int32;
                let memory = intern_c_memory(CMemory::new());
                let pointer = Pointer {
                    block: PointerBlock::Symbolic(Variable(1005500)),
                    offset: PointerOffsetTerm::Constant(0),
                };
                let variable =
                    crate::kernel::eval::load_variable_for_cell(&memory, &pointer, LoadKind::Int32);
                let one = MachineTerm::constant(1);
                let facts = ProofFacts::from_ordered(&[Proposition::ConditionIs(
                    ConditionTerm::equal(MachineTerm::Variable(variable), one.clone()),
                    true,
                )]);
                let mut left = KernelTerm::variable(KernelType::C(ProgramType::Int32), variable);
                let mut right = KernelTermImport::default().machine(format, &one);
                let guard = |value: MachineTerm| {
                    KernelTermImport::default().condition(&ConditionTerm::Compare {
                        format,
                        relation: CompareRelation::GreaterThan,
                        left: Box::new(value),
                        right: Box::new(0u32.into()),
                    })
                };
                let guards = [guard(MachineTerm::Variable(variable)), guard(one.clone())];
                let goal = |root| {
                    Proposition::ConditionIs(
                        ConditionTerm::IntegerEqual(
                            IntegerTerm::Machine(
                                SharedMachineIntegerTerm::from_shared(format, root).unwrap(),
                            )
                            .into(),
                            IntegerTerm::constant_i64(0).into(),
                        ),
                        true,
                    )
                };
                let exports = KernelTermExport::machine_export_count();
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    for i in 0..size {
                        for (root, guard) in [(&mut left, &guards[0]), (&mut right, &guards[1])] {
                            *root = if conditional {
                                KernelTerm::machine_if_shared(
                                    format,
                                    [guard.clone(), root.clone(), root.clone()],
                                )
                            } else {
                                KernelTerm::machine_binary_shared(
                                    format,
                                    MachineBinaryOp::Add,
                                    [root.clone(), root.clone()],
                                )
                            };
                        }
                        if prefixes || i + 1 == size {
                            assert!(
                                facts
                                    .with_checked_rewritten_loads(
                                        &goal(left.clone()),
                                        &goal(right.clone())
                                    )
                                    .is_some()
                            );
                        }
                    }
                });
                let (a, b) = (goal(left), goal(right));
                // A warm syntax cache is no authority for another proof branch.
                assert!(
                    ProofFacts::default()
                        .with_checked_rewritten_loads(&a, &b)
                        .is_none()
                );
                let bind = |body| Proposition::ForAll {
                    name: Default::default(),
                    var: Variable(1005501),
                    sort: Sort::CInt32,
                    body: Box::new(body),
                };
                assert!(
                    facts
                        .with_checked_rewritten_loads(&bind(a.clone()), &bind(b.clone()))
                        .is_none()
                );
                crate::kernel::eval::clear_load_variable_registry();
                assert!(facts.with_checked_rewritten_loads(&a, &b).is_none());
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                samples.push(work);
            }
            for pair in samples.windows(2) {
                assert!(
                    pair[1] <= pair[0] * 5,
                    "conditional={conditional}, prefixes={prefixes}: {samples:?}"
                );
            }
        }
    }
}

#[test]
fn mixed_read_mismatch_keeps_large_shared_operands_unexported() {
    let mut samples = Vec::new();
    for depth in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let mut root = KernelTerm::variable(KernelType::C(ty.c_type()), Variable(1007350));
        for _ in 0..depth {
            root =
                KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [root.clone(), root]);
        }
        let a = observed(SharedMachineIntegerTerm::from_shared(ty, root).unwrap());
        let b = observed(SharedMachineIntegerTerm::intern(
            ty,
            MachineTerm::If {
                condition: ConditionTerm::Variable(Variable(1007351)).into(),
                then_term: MachineTerm::constant(1).into(),
                else_term: MachineTerm::constant(2).into(),
            },
        ));
        let before = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(
                ProofFacts::default()
                    .with_checked_rewritten_loads(&a, &b)
                    .is_none()
            );
            assert!(
                ProofFacts::default()
                    .with_checked_rewritten_loads(&b, &a)
                    .is_none()
            );
        });
        assert_eq!(KernelTermExport::machine_export_count(), before);
        samples.push(work);
    }
    assert!(samples.iter().all(|w| *w == samples[0]), "{samples:?}");
}
