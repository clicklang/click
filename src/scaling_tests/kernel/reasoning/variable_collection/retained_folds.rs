use super::*;
use crate::kernel::{KernelFoldIndex, KernelIntegerOperator, KernelTermExport};

#[test]
fn common_fold_scope_readers_visit_shared_bodies_once_without_exports() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|n| KernelTerm::variable(KernelType::Integer, Variable(970000 + n)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let free = KernelTerm::variable(KernelType::Integer, Variable(971000));
            let mut body = free.clone();
            for _ in 0..size {
                body = KernelTerm::integer_operation(
                    KernelIntegerOperator::Add,
                    vec![body.clone(), body],
                )
                .unwrap();
            }
            let fold = KernelFold::new(
                KernelFoldIndex::Integer,
                Variable(971001),
                Variable(971002),
                [free.clone(), free.clone(), free.clone(), body],
            )
            .unwrap();
            let exports = KernelTermExport::machine_export_count();
            for mode in [
                FoldVariableRead::IntegerFree,
                FoldVariableRead::ExpressionFree,
                FoldVariableRead::MachineCapture,
                FoldVariableRead::IntegerBinders,
                FoldVariableRead::MachineBinders,
            ] {
                let mut variables = BTreeSet::new();
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    collect_fold_variables(&fold, mode, &mut variables)
                });
                assert!(
                    work <= 8 * (size + 1) + 64,
                    "mode={mode:?}, size={size}, unrelated={unrelated}, work={work}"
                );
                match mode {
                    FoldVariableRead::IntegerFree | FoldVariableRead::ExpressionFree => {
                        assert_eq!(variables, BTreeSet::from([Variable(971000)]))
                    }
                    FoldVariableRead::IntegerBinders => assert_eq!(
                        variables,
                        BTreeSet::from([Variable(971001), Variable(971002)])
                    ),
                    _ => assert!(variables.is_empty()),
                }
            }
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
}

#[test]
fn common_fold_scope_summaries_share_growing_variable_sets_between_initial_and_body() {
    let mut costs = Vec::new();
    for size in [16, 64, 256] {
        let mut body = KernelTerm::variable(KernelType::Integer, Variable(973000));
        for index in 1..size {
            body = KernelTerm::integer_operation(
                KernelIntegerOperator::Add,
                vec![
                    body,
                    KernelTerm::variable(KernelType::Integer, Variable(973000 + index)),
                ],
            )
            .unwrap();
        }
        let zero = KernelTerm::integer_literal(0.into());
        // The initial value is outside both binders even though it is the
        // exact same DAG root as the body. Its variables must remain free.
        let fold = KernelFold::new(
            KernelFoldIndex::Integer,
            Variable(973000),
            Variable(973001),
            [zero.clone(), zero, body.clone(), body],
        )
        .unwrap();
        let mut variables = BTreeSet::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            collect_fold_variables(&fold, FoldVariableRead::IntegerFree, &mut variables)
        });
        assert_eq!(variables.len(), size as usize);
        assert!(variables.contains(&Variable(973000)));
        assert!(variables.contains(&Variable(973001)));
        costs.push(work);
    }
    for pair in costs.windows(2) {
        assert!(pair[1] <= 6 * pair[0] + 32, "work={costs:?}");
    }
}

use crate::kernel::{
    AddressBase, KernelAddressOffset, LoadKind, MachineBinaryOp, MachineIntegerType, ProgramType,
    SharedAddress, SharedAddressBase, VerificationSession,
};

#[test]
fn shared_read_capture_visits_address_dags_and_nested_read_prefixes_once() {
    let _session = VerificationSession::enter();
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| {
                KernelTerm::variable(
                    KernelType::Program(ProgramType::Int32),
                    Variable(1016500 + i),
                )
            })
            .collect::<Vec<_>>();
        let memory = crate::kernel::intern_memory(crate::kernel::SymbolicMemory::new());
        let blocks = [1016100, 1016101]
            .map(|id| SharedAddressBase::new(AddressBase::Symbolic(Variable(id))));
        for size in [16, 64, 256] {
            let variable = Variable(1016102);
            let mut root = KernelTerm::variable(KernelType::Program(ProgramType::Int32), variable);
            for _ in 0..size {
                let offset = KernelAddressOffset::Int32Scaled {
                    value: root,
                    byte_width: 4,
                }
                .into_shared()
                .unwrap();
                let children = blocks.each_ref().map(|block| {
                    let address = SharedAddress::new(block.clone(), offset.clone());
                    KernelTerm::shared_scalar_read_descriptor(
                        MachineIntegerType::Int32,
                        &crate::kernel::ProgramPoint::at(&memory),
                        &address,
                        LoadKind::Int32,
                    )
                });
                root = KernelTerm::machine_binary_shared(
                    MachineIntegerType::Int32,
                    MachineBinaryOp::Add,
                    children,
                );
            }
            let exports = crate::kernel::KernelTermExport::machine_export_count();
            for mode in [
                FoldVariableRead::IntegerFree,
                FoldVariableRead::MachineCapture,
                FoldVariableRead::IntegerBinders,
                FoldVariableRead::MachineBinders,
            ] {
                let (variables, work) = crate::instrumentation::measure_deterministic_work(|| {
                    common_variables(&root, mode, &mut Default::default())
                });
                let expected: BTreeSet<_> = if mode == FoldVariableRead::MachineCapture {
                    [Variable(1016100), Variable(1016101), variable]
                        .into_iter()
                        .collect()
                } else {
                    BTreeSet::new()
                };
                assert_eq!(variables.iter().copied().collect::<BTreeSet<_>>(), expected);
                assert!(
                    work <= 40 * size + 100,
                    "mode={mode:?}, size={size}, unrelated={unrelated}, work={work}"
                );
            }
            assert_eq!(
                crate::kernel::KernelTermExport::machine_export_count(),
                exports
            );
        }
    }
}

#[test]
fn float_arithmetic_reader_summaries_visit_shared_operands_once() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [
            crate::kernel::KernelFloatType::Float32,
            crate::kernel::KernelFloatType::Float64,
        ] {
            let mut root =
                KernelTerm::variable(KernelType::Program(format.program_type()), Variable(999935));
            for _ in 0..size {
                root = KernelTerm::float_binary(
                    format,
                    crate::kernel::FloatBinaryOperator::Add,
                    [root.clone(), root],
                )
                .unwrap();
            }
            for mode in [
                FoldVariableRead::IntegerFree,
                FoldVariableRead::ExpressionFree,
                FoldVariableRead::MachineCapture,
                FoldVariableRead::IntegerBinders,
                FoldVariableRead::MachineBinders,
            ] {
                let mut summaries = Default::default();
                let (_, cold) = crate::instrumentation::measure_deterministic_work(|| {
                    common_variables(&root, mode, &mut summaries)
                });
                let (_, warm) = crate::instrumentation::measure_deterministic_work(|| {
                    common_variables(&root, mode, &mut summaries)
                });
                assert!(
                    cold <= 30 * size + 100,
                    "size={size}, mode={mode:?}, work={cold}"
                );
                assert!(warm <= 2, "warm={warm}");
                assert!(
                    crate::kernel::FloatOperandView::from_shared(&root)
                        .unwrap()
                        .old_form()
                        .is_none()
                );
            }
        }
    }
}

#[test]
fn cached_integer_condition_variable_readers_reuse_the_produced_operands() {
    use crate::kernel::{
        BooleanOperandView, IntegerComparisonOperator, IntegerTerm, KernelTermImport,
        MachineIntegerType, OldMachineTerm, StoredConditionTerm,
    };
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let machine = IntegerTerm::from_machine(
            MachineIntegerType::UInt64,
            OldMachineTerm::Variable(Variable(979101)),
        )
        .unwrap();
        let mut operand = KernelTerm::integer_operation(
            KernelIntegerOperator::Add,
            vec![
                KernelTerm::variable(KernelType::Integer, Variable(979100)),
                KernelTermImport::default().integer(&machine.into()),
            ],
        )
        .unwrap();
        for _ in 0..size {
            operand = KernelTerm::integer_operation(
                KernelIntegerOperator::Add,
                vec![operand.clone(), operand],
            )
            .unwrap();
        }
        let root = KernelTerm::integer_comparison(
            IntegerComparisonOperator::Equal,
            [operand, KernelTerm::integer_literal(0.into())],
        )
        .unwrap();
        let stored = StoredConditionTerm::from_root(root.clone()).unwrap();
        let native = stored.old_form().clone();
        let exports = KernelTermExport::machine_export_count();
        let repeats = 16;
        for mode in [
            FoldVariableRead::IntegerFree,
            FoldVariableRead::ExpressionFree,
            FoldVariableRead::MachineCapture,
            FoldVariableRead::IntegerBinders,
            FoldVariableRead::MachineBinders,
        ] {
            let mut expected = BTreeSet::new();
            let (_, native_work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..repeats {
                    expected.clear();
                    collect_boolean_variables(
                        BooleanOperandView::Native(&native),
                        mode,
                        &mut expected,
                    );
                }
            });
            let mut actual = BTreeSet::new();
            let (_, shared_work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..repeats {
                    actual.clear();
                    collect_boolean_variables(BooleanOperandView::Shared(&root), mode, &mut actual);
                }
            });
            assert_eq!(actual, expected, "mode={mode:?}, size={size}");
            assert!(
                shared_work <= native_work + 4 * repeats,
                "mode={mode:?}, size={size}, native={native_work}, shared={shared_work}"
            );
        }
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}

#[test]
fn minted_scalar_comparison_readers_reuse_selected_native_read_work() {
    use crate::kernel::{
        BooleanOperandView, CompareRelation, OldConditionTerm, OldMachineTerm, StoredConditionTerm,
    };
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let mut offset = OldMachineTerm::Variable(Variable(979200));
        for n in 1..size {
            offset = OldMachineTerm::Binary {
                format: MachineIntegerType::Int32,
                op: MachineBinaryOp::Add,
                left: Box::new(offset),
                right: Box::new(OldMachineTerm::Variable(Variable(979200 + n))),
            };
        }
        let memory = crate::kernel::intern_memory(crate::kernel::SymbolicMemory::new());
        let pointer = Address::new(
            AddressBase::Symbolic(Variable(979199)),
            AddressOffset::scaled_int32_node(offset, 4),
        );
        let native = OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(OldMachineTerm::read_named(
                crate::kernel::ProgramPoint::at(&memory),
                Box::new(pointer),
                LoadKind::Int32,
            )),
            right: Box::new(0.into()),
        };
        let stored = StoredConditionTerm::from_minted(native.clone());
        let root = stored.root().expect("minted scalar comparison");
        let exports = KernelTermExport::machine_export_count();
        let repeats = 8;
        for mode in [
            FoldVariableRead::IntegerFree,
            FoldVariableRead::ExpressionFree,
            FoldVariableRead::MachineCapture,
            FoldVariableRead::IntegerBinders,
            FoldVariableRead::MachineBinders,
        ] {
            let mut expected = BTreeSet::new();
            let (_, native_work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..repeats {
                    expected.clear();
                    collect_boolean_variables(
                        BooleanOperandView::Native(&native),
                        mode,
                        &mut expected,
                    );
                }
            });
            let mut actual = BTreeSet::new();
            let (_, shared_work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..repeats {
                    actual.clear();
                    collect_boolean_variables(BooleanOperandView::Shared(root), mode, &mut actual);
                }
            });
            assert_eq!(actual, expected, "mode={mode:?}, size={size}");
            assert!(
                shared_work <= native_work + 2 * repeats,
                "mode={mode:?}, size={size}, native={native_work}, shared={shared_work}"
            );
        }
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}

#[test]
fn condition_terms_and_mutex_guards_collect_variables_without_native_export() {
    use crate::kernel::{
        CompareRelation, ConditionalMutexGuard, InstanceId, MutexIdentity, StoredConditionTerm,
    };
    for depth in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let machine = Variable(10998565);
        let selector = Variable(10998566);
        let guard = KernelTerm::variable(KernelType::Bool, selector);
        let mut root = KernelTerm::boolean_comparison_raw(
            MachineIntegerType::Int32,
            CompareRelation::Equal,
            [
                KernelTerm::variable(KernelType::Program(ProgramType::Int32), machine),
                KernelTerm::int32_literal(3),
            ],
        );
        for _ in 0..depth {
            root = KernelTerm::boolean_if_raw([
                guard.clone(),
                root,
                KernelTerm::boolean_literal(false),
            ]);
        }
        let held = StoredConditionTerm::from_root(root.clone()).unwrap();
        let term = Term::Condition(held.clone());
        let mutex = MutexIdentity {
            mutex: Address::symbolic(Variable(10998567)),
            epoch: Some(9),
        };
        let resource =
            Resource::ConditionalMutexGuard(std::sync::Arc::new(ConditionalMutexGuard {
                identity: InstanceId::from_variable(Variable(10998568)),
                guard: mutex.clone(),
                initialization: mutex,
                held,
            }));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut variables = BTreeSet::new();
            collect_term_bitvector_variables(&term, &mut variables);
            assert_eq!(variables, BTreeSet::from([machine]));
            variables.clear();
            collect_resource_bitvector_variables(&resource, &mut variables);
            assert_eq!(variables, BTreeSet::from([machine]));
            variables.clear();
            let claim = Proposition::Equal(term.clone(), term.clone());
            collect_proposition_connection_variables(&claim, &mut variables);
            assert_eq!(variables, BTreeSet::from([machine, selector]));
        });
        assert!(work <= 96 * (depth + 1), "depth={depth} work={work}");
        assert!(!root.has_cached_native_argument());
    }
}
