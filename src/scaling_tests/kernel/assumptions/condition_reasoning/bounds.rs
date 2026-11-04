use super::*;
use crate::kernel::{KernelTerm, KernelType, MachineBinaryOp, Variable};

#[test]
fn shared_bound_consumers_preserve_dag_operands() {
    let mut samples = Vec::new();
    for size in [8, 32, 96] {
        for ambient in [0, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let ty = MachineIntegerType::Int32;
            let mut facts = PureFactContext::new();
            for i in 0..ambient {
                facts = facts.assume_condition(
                    ConditionTerm::equal(
                        MachineTerm::Variable(Variable(995000 + i)),
                        MachineTerm::constant(7),
                    ),
                    true,
                );
            }
            let mut root = KernelTerm::variable(KernelType::C(ty.c_type()), Variable(994201));
            let observe = |term| IntegerTerm::from_machine(ty, term).unwrap();
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                for level in 0..size {
                    let x = MachineTerm::Variable(Variable(996000 + level * 2));
                    let y = MachineTerm::Variable(Variable(996001 + level * 2));
                    root = KernelTerm::machine_binary_shared(
                        ty,
                        MachineBinaryOp::Add,
                        [root.clone(), root.clone()],
                    );
                    let operand = SharedMachineIntegerTerm::from_shared(ty, root.clone()).unwrap();
                    let first = ConditionTerm::integer_less_equal(
                        observe(x.clone()),
                        IntegerTerm::Machine(operand.clone()),
                    );
                    let second = ConditionTerm::integer_less_equal(
                        IntegerTerm::Machine(operand.clone()),
                        observe(y.clone()),
                    );
                    facts = facts
                        .assume_condition(first, true)
                        .assume_condition(second, true);
                    assert!(facts.has_upper_bound_at_or_below(&x, &y));
                    assert!(shared_signed_const_add(operand.operand_view(), 1).is_none());
                    assert!(!shared_successor_of(operand.operand_view(), V::Legacy(&y)));
                    assert!(!operand.has_boxed_operand());
                }
            });
            samples.push((size, ambient, work));
        }
    }
    for pair in samples.chunks_exact(2) {
        assert!(pair[1].2 <= pair[0].2 * 2 + 64, "{samples:?}");
    }
    for pair in samples.chunks_exact(2).collect::<Vec<_>>().windows(2) {
        let (small, _, sw) = pair[0][0];
        let (large, _, lw) = pair[1][0];
        assert!(
            lw * small as usize <= sw * large as usize * 2,
            "{samples:?}"
        );
    }
}

#[test]
fn shared_comparison_class_queries_do_not_export_dag_prefixes() {
    let mut samples = Vec::new();
    for size in [8, 32, 96] {
        // Both samples have order classes: an entirely empty graph can skip
        // registration by kind, which is a different path from a keyed miss.
        for ambient in [1, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let ty = MachineIntegerType::Int32;
            let mut facts = PureFactContext::new();
            for i in 0..ambient {
                facts = facts.assume_condition(
                    ConditionTerm::signed_less_equal(
                        MachineTerm::Variable(Variable(997000 + i)),
                        MachineTerm::constant(7),
                    ),
                    true,
                );
            }
            let mut root = KernelTerm::variable(KernelType::C(ty.c_type()), Variable(994401));
            let right = MachineTerm::Variable(Variable(994402));
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                for level in 0..size {
                    root = KernelTerm::machine_binary_shared(
                        ty,
                        MachineBinaryOp::Add,
                        [root.clone(), root.clone()],
                    );
                    let operand = SharedMachineIntegerTerm::from_shared(ty, root.clone()).unwrap();
                    let query = ConditionTerm::integer_less_equal(
                        IntegerTerm::Machine(operand.clone()),
                        IntegerTerm::from_machine(ty, right.clone()).unwrap(),
                    );
                    assert!(!facts.equality_graph.knows_condition(&query, true));
                    assert!(!facts.equality_graph.knows_condition(&query, false));
                    assert!(!operand.has_boxed_operand());
                    let alias = MachineTerm::Variable(Variable(998000 + level));
                    let child = facts
                        .clone()
                        .assume_condition(
                            ConditionTerm::integer_equal(
                                IntegerTerm::Machine(operand.clone()),
                                IntegerTerm::from_machine(ty, alias.clone()).unwrap(),
                            ),
                            true,
                        )
                        .assume_condition(
                            ConditionTerm::signed_less_equal(alias, right.clone()),
                            true,
                        );
                    // This is the full dispatcher, through an equality alias
                    // rather than an exact observation-index hit.
                    assert_eq!(child.decide(&query), Some(true));
                    assert!(!operand.has_boxed_operand());
                    assert!(!facts.equality_graph.knows_condition(&query, true));
                    assert!(!operand.has_boxed_operand());
                }
            });
            samples.push((size, ambient, work));
        }
    }
    for pair in samples.chunks_exact(2) {
        assert!(pair[1].2 <= pair[0].2 * 2 + 64, "{samples:?}");
    }
    for pair in samples.chunks_exact(2).collect::<Vec<_>>().windows(2) {
        let (small, _, sw) = pair[0][0];
        let (large, _, lw) = pair[1][0];
        assert!(
            lw * small as usize <= sw * large as usize * 2,
            "{samples:?}"
        );
    }
}

#[test]
fn shared_exact_order_walk_visits_dag_endpoints_once() {
    let mut samples = Vec::new();
    for size in [8, 32, 96] {
        for ambient in [0, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let ty = MachineIntegerType::Int32;
            let variable = KernelTerm::variable(KernelType::C(ty.c_type()), Variable(997001));
            let first = SharedMachineIntegerTerm::from_shared(
                ty,
                KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [variable.clone(), variable],
                ),
            )
            .unwrap();
            let mut last = first.clone();
            let mut roots = vec![first.clone()];
            let mut facts = PureFactContext::new();
            for i in 0..ambient {
                facts = facts.assume_condition(
                    ConditionTerm::signed_less_than(
                        MachineTerm::Variable(Variable(998000 + i * 2)),
                        MachineTerm::Variable(Variable(998001 + i * 2)),
                    ),
                    true,
                );
            }
            for _ in 0..size {
                let V::Shared(root) = last.operand_view() else {
                    panic!("shared root")
                };
                let next = SharedMachineIntegerTerm::from_shared(
                    ty,
                    KernelTerm::machine_binary_shared(
                        ty,
                        MachineBinaryOp::Add,
                        [root.clone(), root.clone()],
                    ),
                )
                .unwrap();
                facts = facts.assume_condition(
                    ConditionTerm::integer_less_than(
                        IntegerTerm::Machine(last),
                        IntegerTerm::Machine(next.clone()),
                    ),
                    true,
                );
                roots.push(next.clone());
                last = next;
            }
            assert!(
                roots.iter().all(|root| !root.has_boxed_operand()),
                "admission exported an endpoint"
            );
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                assert!(facts.has_exact_order_path_views(
                    first.operand_view(),
                    last.operand_view(),
                    true
                ));
                let missing = KernelTerm::variable(KernelType::C(ty.c_type()), Variable(997002));
                assert!(!facts.has_exact_order_path_views(
                    first.operand_view(),
                    V::Shared(&missing),
                    true
                ));
            });
            assert!(roots.iter().all(|root| !root.has_boxed_operand()));
            samples.push((size, ambient, work));
        }
    }
    for pair in samples.chunks_exact(2) {
        assert_eq!(pair[0].2, pair[1].2, "{samples:?}");
    }
    for pair in samples.chunks_exact(2).collect::<Vec<_>>().windows(2) {
        let (small, _, sw) = pair[0][0];
        let (large, _, lw) = pair[1][0];
        assert!(lw * small <= sw * large * 2, "{samples:?}");
    }
}
