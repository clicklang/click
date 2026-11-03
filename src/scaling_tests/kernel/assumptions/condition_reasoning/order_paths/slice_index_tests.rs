// Scaling tests of `src/kernel/assumptions/condition_reasoning/order_paths.rs` (module `slice_index_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn wide_order_chain_work_follows_the_chain_and_not_unrelated_facts() {
    let v = |n: u64| Bitvector32Term::Variable(Variable(996000 + n));
    let lt = ConditionTerm::uint64_less_than;
    let u = Bitvector32Term::UInt64Constant;
    // A chain of fixed length beside a growing set of unrelated facts,
    // some sharing a literal endpoint with the question.
    let mut beside = Vec::new();
    for size in [2, 4, 8, 16] {
        let mut facts = PureFactContext::new();
        for i in 0..4 {
            facts = facts.assume_condition(lt(v(i), v(i + 1)), true);
        }
        facts = facts.assume_condition(lt(v(4), u(1000)), true);
        for i in 0..size {
            facts = facts
                .assume_condition(lt(v(10_000 + i), v(20_000 + i)), true)
                .assume_condition(lt(u(0), v(30_000 + i)), true)
                .assume_condition(lt(v(40_000 + i), u(1000)), true);
        }
        let (answers, work) = crate::instrumentation::measure_deterministic_work(|| {
            [
                facts.decide(&lt(v(0), v(4))),
                facts.decide(&lt(v(0), u(1000))),
                facts.decide(&lt(v(4), v(0))),
            ]
        });
        assert_eq!(answers, [Some(true), Some(true), Some(false)]);
        beside.push(work);
    }
    assert!(beside.iter().all(|work| *work == beside[0]), "{beside:?}");
    // A growing chain costs work linear in its length. The difference
    // graph answers a chain of at most `EDGE_LIMIT` edges; a longer one is
    // left to the order walk, which costs more per edge. Each regime is
    // checked on its own sizes, so the step between them is not read as
    // growth.
    let limit = crate::kernel::difference_graph::EDGE_LIMIT as u64;
    for sizes in [
        [limit / 4, limit / 2, limit].as_slice(),
        &[2 * limit, 4 * limit, 8 * limit, 16 * limit],
    ] {
        let mut along = Vec::new();
        for &size in sizes {
            let mut facts = PureFactContext::new();
            for i in 0..size {
                facts = facts.assume_condition(lt(v(i), v(i + 1)), true);
            }
            let (answer, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.decide(&lt(v(0), v(size)))
            });
            assert_eq!(answer, Some(true));
            along.push((size, work));
        }
        for pair in along.windows(2) {
            assert!(pair[1].1 <= 3 * pair[0].1, "{along:?}");
        }
    }
}

#[test]
fn uint64_constant_order_strengthening_is_sound_at_full_width_and_scales() {
    let n = Bitvector32Term::Variable(Variable(998001));
    let c = Bitvector32Term::UInt64Constant;
    let mut work_counts = Vec::new();
    for size in [8, 32, 128] {
        let mut facts = PureFactContext::new();
        for i in 0..size {
            // Shared endpoints exercise the dangerous constant-index shape.
            facts = facts.assume_condition(
                ConditionTerm::uint64_less_than(
                    c(0),
                    Bitvector32Term::Variable(Variable(999000 + i)),
                ),
                true,
            );
        }
        facts = facts.assume_condition(
            ConditionTerm::uint64_greater_than(n.clone(), c(4294967295)),
            true,
        );
        let (answers, work) = crate::instrumentation::measure_deterministic_work(|| {
            [
                facts.decide(&ConditionTerm::uint64_less_than(n.clone(), c(253))),
                facts.decide(&ConditionTerm::uint64_less_equal(n.clone(), c(65535))),
                facts.decide(&ConditionTerm::uint64_less_than(c(0), n.clone())),
                facts.decide(&ConditionTerm::uint64_equal(n.clone(), c(0))),
            ]
        });
        assert_eq!(answers, [Some(false), Some(false), Some(true), Some(false)]);
        work_counts.push(work);
    }
    assert!(work_counts[0] > 0);
    assert!(
        work_counts.iter().all(|work| *work == work_counts[0]),
        "{work_counts:?}"
    );
    for bound in [
        0,
        253,
        65535,
        4294967295,
        i64::MAX as u64,
        i64::MAX as u64 + 1,
        u64::MAX,
    ] {
        let facts = PureFactContext::new()
            .assume_condition(ConditionTerm::uint64_less_equal(n.clone(), c(bound)), true);
        assert_eq!(
            facts.decide(&ConditionTerm::uint64_greater_than(n.clone(), c(bound))),
            Some(false)
        );
        if bound < u64::MAX {
            assert_eq!(
                facts.decide(&ConditionTerm::uint64_less_than(n.clone(), c(bound + 1))),
                Some(true)
            );
            assert_eq!(
                facts.decide(&ConditionTerm::uint64_equal(n.clone(), c(bound + 1))),
                Some(false)
            );
        }
        assert_ne!(
            facts.decide(&ConditionTerm::uint64_less_than(n.clone(), c(bound))),
            Some(true)
        );
    }
    let negative = PureFactContext::new()
        .assume_condition(ConditionTerm::uint64_less_equal(n.clone(), c(65535)), false);
    assert_eq!(
        negative.decide(&ConditionTerm::uint64_less_than(n.clone(), c(253))),
        Some(false)
    );
    assert_eq!(
        PureFactContext::new().decide(&ConditionTerm::uint64_less_than(n, c(253))),
        None
    );
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn uint64_slice_remainder_bounds_ignore_unrelated_facts() {
    let length = Bitvector32Term::Variable(Variable(993001));
    let midpoint = Bitvector32Term::Variable(Variable(993002));
    let difference = Bitvector32Term::uint64_subtract(length.clone(), midpoint.clone());
    let positive =
        ConditionTerm::uint64_less_than(Bitvector32Term::UInt64Constant(0), difference.clone());
    let bounded = ConditionTerm::uint64_less_equal(difference, length.clone());
    let mut work = Vec::new();
    for size in [1, 4, 16, 64] {
        let mut context = PureFactContext::new();
        for n in 0..size {
            context = context.assume_condition(
                ConditionTerm::uint64_less_equal(
                    Bitvector32Term::Variable(Variable(994000 + n)),
                    Bitvector32Term::UInt64Constant(100),
                ),
                true,
            );
        }
        context = context.assume_condition(
            ConditionTerm::uint64_less_than(midpoint.clone(), length.clone()),
            true,
        );
        let (_, used) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                context
                    .selected_for_test()
                    .decide_selected_condition(&positive),
                Some(true)
            );
            assert_eq!(
                context
                    .selected_for_test()
                    .decide_selected_condition(&bounded),
                Some(true)
            );
        });
        work.push(used);
    }
    assert!(work.iter().all(|used| *used == work[0]), "{work:?}");
    let unbounded = PureFactContext::new();
    assert_ne!(
        unbounded
            .selected_for_test()
            .decide_selected_condition(&positive),
        Some(true)
    );
    assert_ne!(
        unbounded
            .selected_for_test()
            .decide_selected_condition(&bounded),
        Some(true)
    );
    let underflow = PureFactContext::new()
        .assume_condition(ConditionTerm::uint64_greater_than(midpoint, length), true);
    assert_ne!(
        underflow
            .selected_for_test()
            .decide_selected_condition(&bounded),
        Some(true)
    );
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn uint64_slice_index_transport_is_sound_and_ignores_unrelated_bounds() {
    let index = Bitvector32Term::Variable(Variable(991001));
    let length = Bitvector32Term::Variable(Variable(991002));
    let index_word = Bitvector32Term::uint32_from_64(index.clone());
    let length_word = Bitvector32Term::uint32_from_64(length.clone());
    let goal = ConditionTerm::signed_less_than(index_word.clone(), length_word);
    let mut work = Vec::new();
    for size in [8, 32, 128] {
        let mut context = PureFactContext::new();
        for n in 0..size {
            context = context.assume_condition(
                ConditionTerm::uint64_less_equal(
                    Bitvector32Term::Variable(Variable(992000 + n)),
                    Bitvector32Term::UInt64Constant(100),
                ),
                true,
            );
        }
        context = context
            .assume_condition(
                ConditionTerm::uint64_less_than(index.clone(), length.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::uint64_less_equal(
                    length.clone(),
                    Bitvector32Term::UInt64Constant(i32::MAX as u64),
                ),
                true,
            );
        let (_, used) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(context.decide_small_uint64_index_order(&goal), Some(true));
            assert_eq!(
                context.decide_small_uint64_index_order(&ConditionTerm::signed_less_equal(
                    Bitvector32Term::Constant(0),
                    index_word.clone()
                )),
                Some(true)
            );
        });
        work.push(used);
    }
    // Unrelated bounds must not increase work; cheaper lookups are allowed.
    assert!(work.iter().all(|used| *used <= work[0]), "{work:?}");
    let unbounded = PureFactContext::new().assume_condition(
        ConditionTerm::uint64_less_than(index.clone(), length.clone()),
        true,
    );
    assert_eq!(unbounded.decide_small_uint64_index_order(&goal), None);
    let high = unbounded.assume_condition(
        ConditionTerm::uint64_less_equal(length, Bitvector32Term::UInt64Constant(4294967296)),
        true,
    );
    assert_eq!(high.decide_small_uint64_index_order(&goal), None);
    let reversed = PureFactContext::new()
        .assume_condition(
            ConditionTerm::uint64_less_equal(index.clone(), Bitvector32Term::UInt64Constant(10)),
            true,
        )
        .assume_condition(
            ConditionTerm::uint64_less_equal(
                Bitvector32Term::Variable(Variable(991002)),
                Bitvector32Term::UInt64Constant(10),
            ),
            true,
        )
        .assume_condition(
            ConditionTerm::uint64_greater_equal(index, Bitvector32Term::Variable(Variable(991002))),
            true,
        );
    assert_eq!(reversed.decide_small_uint64_index_order(&goal), Some(false));
}

#[test]
fn shared_wide_order_walks_scale_with_selected_chain() {
    use crate::kernel::{KernelTerm, KernelType, SharedMachineIntegerTerm};
    let mut samples = Vec::new();
    for size in [8, 24, 72] {
        for unrelated in [0, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let ty = MachineIntegerType::UInt64;
            let operand = |id| {
                let root = KernelTerm::variable(KernelType::C(ty.c_type()), Variable(id));
                SharedMachineIntegerTerm::from_shared(
                    ty,
                    KernelTerm::machine_binary_shared(
                        ty,
                        crate::kernel::MachineBinaryOp::Add,
                        [root.clone(), root],
                    ),
                )
                .unwrap()
            };
            let terms: Vec<_> = (0..=size).map(|i| operand(999100 + i)).collect();
            let observe = |term: &SharedMachineIntegerTerm| IntegerTerm::Machine(term.clone());
            let mut parent = PureFactContext::new();
            for i in 0..unrelated {
                parent = parent.assume_condition(
                    ConditionTerm::integer_less_than(
                        observe(&operand(999300 + i)),
                        IntegerTerm::constant(99.into()),
                    ),
                    true,
                );
            }
            let mut context = parent.clone();
            for pair in terms.windows(2) {
                context = context.assume_condition(
                    ConditionTerm::integer_less_than(observe(&pair[0]), observe(&pair[1])),
                    true,
                );
            }
            let last = terms.last().unwrap();
            let goal = ConditionTerm::integer_less_than(observe(&terms[0]), observe(last));
            let reverse = ConditionTerm::integer_less_equal(observe(last), observe(&terms[0]));
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                assert_eq!(context.decide_wide_order_chain(&goal), Some(true));
                assert_eq!(context.decide_wide_order_chain(&reverse), Some(false));
                assert_eq!(parent.decide_wide_order_chain(&goal), None);
            });
            assert!(terms.iter().all(|term| !term.has_boxed_operand()));
            samples.push((size as usize, unrelated, work));
        }
    }
    for pair in samples.chunks_exact(2) {
        assert!(pair[1].2 <= pair[0].2 + 32, "{samples:?}");
    }
    for pair in samples.chunks_exact(2).collect::<Vec<_>>().windows(2) {
        let (small, _, sw) = pair[0][0];
        let (large, _, lw) = pair[1][0];
        assert!(lw * small <= sw * large * 2, "{samples:?}");
    }
}

#[test]
fn signed_order_views_preserve_native_answers_without_exporting() {
    use crate::kernel::{KernelTermExport, KernelTermImport, SharedMachineIntegerTerm};
    let _session = crate::kernel::VerificationSession::enter();
    let x = Bitvector32Term::Variable(Variable(996701));
    let y = Bitvector32Term::Variable(Variable(996702));
    let contexts = [
        PureFactContext::new(),
        PureFactContext::new()
            .assume_condition(ConditionTerm::signed_less_equal(0.into(), x.clone()), true)
            .assume_condition(ConditionTerm::signed_less_equal(x.clone(), 10.into()), true)
            .assume_condition(ConditionTerm::signed_less_than(x.clone(), y.clone()), true),
    ];
    let values = [
        x.clone(),
        y,
        Bitvector32Term::add(x.clone(), 1.into()),
        Bitvector32Term::subtract(x, 1.into()),
        0.into(),
        12.into(),
    ];
    let shared: Vec<_> = values
        .iter()
        .map(|term| {
            SharedMachineIntegerTerm::from_shared(
                MachineIntegerType::Int32,
                KernelTermImport::default()
                    .machine_arithmetic(MachineIntegerType::Int32, term)
                    .unwrap(),
            )
            .unwrap()
        })
        .collect();
    for facts in contexts {
        for (i, left) in values.iter().enumerate() {
            for (j, right) in values.iter().enumerate() {
                for relation in [
                    CompareRelation::LessThan,
                    CompareRelation::LessEqual,
                    CompareRelation::GreaterThan,
                    CompareRelation::GreaterEqual,
                ] {
                    let native = facts.decide_signed_order_views(
                        relation,
                        MachineOperandView::Legacy(left),
                        MachineOperandView::Legacy(right),
                    );
                    let exports = KernelTermExport::machine_export_count();
                    let retained = facts.decide_signed_order_views(
                        relation,
                        shared[i].operand_view(),
                        shared[j].operand_view(),
                    );
                    assert_eq!(native, retained, "{relation:?}: {left:?}, {right:?}");
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                }
            }
        }
    }
}

#[test]
fn signed_order_rules_keep_growing_shared_prefixes() {
    use crate::kernel::{KernelTerm, KernelTermExport, KernelType, SharedMachineIntegerTerm};
    let mut samples = Vec::new();
    for size in [4, 12, 36] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut root = KernelTerm::variable(KernelType::C(format.c_type()), Variable(996711));
        let mut facts = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                root = KernelTerm::machine_binary_shared(
                    format,
                    crate::kernel::MachineBinaryOp::Add,
                    [root.clone(), root.clone()],
                );
                let operand = SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap();
                facts = facts.assume_condition(
                    ConditionTerm::equal(
                        Bitvector32Term::Variable(Variable(996720 + index)),
                        7.into(),
                    ),
                    true,
                );
                // Each step changes the context. Reflexive and extreme rules
                // must inspect roots without visiting the growing prefix.
                assert_eq!(
                    facts.decide_signed_order_views(
                        CompareRelation::LessThan,
                        operand.operand_view(),
                        operand.operand_view()
                    ),
                    Some(false)
                );
                assert_eq!(
                    facts.decide_signed_order_views(
                        CompareRelation::LessEqual,
                        MachineOperandView::Legacy(&Bitvector32Term::Constant(i32::MIN as u32)),
                        operand.operand_view()
                    ),
                    Some(true)
                );
                assert!(!operand.has_boxed_operand());
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push((size as usize, work));
    }
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small * 4 <= sw * large * 5, "{samples:?}");
    }
}

#[test]
fn unsigned_order_views_preserve_native_answers_and_polarity() {
    use crate::kernel::{KernelTermExport, KernelTermImport, SharedMachineIntegerTerm};
    let _session = crate::kernel::VerificationSession::enter();
    let x = Bitvector32Term::Variable(Variable(996761));
    let y = Bitvector32Term::Variable(Variable(996762));
    let sum = Bitvector32Term::add_at(MachineIntegerType::UInt32, x.clone(), 1.into());
    let facts = PureFactContext::new()
        .assume_condition(
            ConditionTerm::unsigned_greater_than(y.clone(), sum.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::unsigned_greater_than(x.clone(), y.clone()),
            false,
        );
    let values = [x, sum, y, 0.into(), Bitvector32Term::Constant(u32::MAX)];
    let shared: Vec<_> = values
        .iter()
        .map(|term| {
            SharedMachineIntegerTerm::from_shared(
                MachineIntegerType::UInt32,
                KernelTermImport::default()
                    .machine_arithmetic(MachineIntegerType::UInt32, term)
                    .unwrap(),
            )
            .unwrap()
        })
        .collect();
    for (i, left) in values.iter().enumerate() {
        for (j, right) in values.iter().enumerate() {
            for strict in [true, false] {
                let native = facts.decide_unsigned32_order_views(
                    MachineOperandView::Legacy(left),
                    MachineOperandView::Legacy(right),
                    strict,
                );
                let exports = KernelTermExport::machine_export_count();
                let retained = facts.decide_unsigned32_order_views(
                    shared[i].operand_view(),
                    shared[j].operand_view(),
                    strict,
                );
                assert_eq!(native, retained, "{left:?}, {right:?}, strict={strict}");
                assert_eq!(KernelTermExport::machine_export_count(), exports);
            }
        }
    }
}

#[test]
fn shared_successor_transport_uses_ordinary_dispatch_without_export() {
    use crate::kernel::{
        IntegerTerm, KernelTermExport, KernelTermImport, SharedMachineIntegerTerm,
    };
    let _session = crate::kernel::VerificationSession::enter();
    let x = Bitvector32Term::Variable(Variable(996781));
    let y = Bitvector32Term::Variable(Variable(996782));
    let facts = PureFactContext::new()
        .assume_condition(ConditionTerm::signed_less_than(x.clone(), y.clone()), true);
    let successor = Bitvector32Term::add(x, 1.into());
    let shared = SharedMachineIntegerTerm::from_shared(
        MachineIntegerType::Int32,
        KernelTermImport::default()
            .machine_arithmetic(MachineIntegerType::Int32, &successor)
            .unwrap(),
    )
    .unwrap();
    let query = ConditionTerm::integer_less_equal(
        IntegerTerm::Machine(shared.clone()),
        IntegerTerm::from_machine(MachineIntegerType::Int32, y).unwrap(),
    );
    let exports = KernelTermExport::machine_export_count();
    assert_eq!(facts.decide(&query), Some(true));
    assert_eq!(KernelTermExport::machine_export_count(), exports);
    assert!(!shared.has_boxed_operand());
}
