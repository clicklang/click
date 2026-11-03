// Scaling tests of `src/kernel/assumptions/condition_reasoning/overflow_intervals.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::{MachineIntegerType, OverflowOperation};

#[test]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn widened_unsigned_sum_bounds_are_sound_and_flat_in_unrelated_facts() {
    let a = Bitvector32Term::Variable(Variable(97001));
    let b = Bitvector32Term::Variable(Variable(97002));
    let sum = Bitvector32Term::int64_add(
        Bitvector32Term::int64_from_uint32(a.clone()),
        Bitvector32Term::int64_from_uint32(b.clone()),
    );
    let goal = ConditionTerm::int64_signed_less_equal(
        sum.clone(),
        Bitvector32Term::int64_constant(u32::MAX as i64),
    );
    let too_small = ConditionTerm::int64_signed_less_equal(
        sum,
        Bitvector32Term::int64_constant(u32::MAX as i64 - 1),
    );
    let mut works = Vec::new();
    for size in [8, 32, 128] {
        let mut facts = PureFactContext::new();
        for index in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::unsigned_less_equal(
                    Bitvector32Term::Variable(Variable(98000 + index)),
                    Bitvector32Term::constant(123),
                ),
                true,
            );
        }
        facts = facts
            .assume_condition(
                ConditionTerm::unsigned_less_equal(
                    a.clone(),
                    Bitvector32Term::constant(u32::MAX - 255),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_greater_equal(b.clone(), Bitvector32Term::constant(0)),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(b.clone(), Bitvector32Term::constant(255)),
                true,
            );
        let (answer, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.decide_widened_sum_bound(&goal)
        });
        assert_eq!(answer, Some(true));
        assert_eq!(facts.decide_widened_sum_bound(&too_small), None);
        let selected = facts.widened_unsigned_sum_bound_premises(&goal).unwrap();
        let selected_context = selected
            .iter()
            .fold(PureFactContext::new(), |context, premise| {
                context.assume_proposition(premise.clone())
            });
        assert_eq!(selected_context.decide_widened_sum_bound(&goal), Some(true));
        use crate::kernel::proof::arithmetic_special::{
            SpecialArithmeticCertificate, SpecialArithmeticNode,
        };
        let certificate = SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::UnsignedSumBound {
                bounds: (0..selected.len()).collect(),
                result: Proposition::ConditionIs(goal.clone(), true),
            }],
            conclusion: 0,
        };
        certificate
            .check(&Proposition::ConditionIs(goal.clone(), true), &selected)
            .unwrap();
        let forged = SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::UnsignedSumBound {
                bounds: (0..selected.len()).collect(),
                result: Proposition::ConditionIs(too_small.clone(), true),
            }],
            conclusion: 0,
        };
        assert!(
            forged
                .check(
                    &Proposition::ConditionIs(too_small.clone(), true),
                    &selected
                )
                .is_err()
        );
        let invalid =
            ConditionTerm::unsigned_greater_equal(b.clone(), Bitvector32Term::constant(256));
        // Query the native unsigned order using its indexed unsigned bound.
        let facts = facts.assume_condition(
            ConditionTerm::unsigned_less_than(b.clone(), Bitvector32Term::constant(8)),
            true,
        );
        let (answer, order_work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.decide_from_order_facts(&invalid)
        });
        assert_eq!(answer, Some(false));
        works.push(work + order_work);
    }
    assert!(works.iter().all(|work| *work == works[0]), "{works:?}");
    let unknown = PureFactContext::new();
    assert_eq!(unknown.decide_widened_sum_bound(&goal), None);
}

/// The `int32_defined` / `int64_defined` closer selects each operand's
/// constant bounds by keyed lookup. Its deterministic work must be flat
/// in the number of unrelated constant-bound facts of either width, and
/// the selected facts must satisfy the kernel checker.
#[test]
fn signed_constant_bound_selection_is_flat_in_unrelated_bounds() {
    use crate::kernel::proof::arithmetic_special::{
        SpecialArithmeticCertificate, SpecialArithmeticNode,
    };
    for width in [SignedDefinedWidth::Int32, SignedDefinedWidth::Int64] {
        let constant = |value: i64| match width {
            SignedDefinedWidth::Int32 => Bitvector32Term::constant(value as i32 as u32),
            SignedDefinedWidth::Int64 => Bitvector32Term::int64_constant(value),
        };
        let less = |left, right| match width {
            SignedDefinedWidth::Int32 => ConditionTerm::signed_less_than(left, right),
            SignedDefinedWidth::Int64 => ConditionTerm::int64_signed_less_than(left, right),
        };
        let at_least = |left, right| match width {
            SignedDefinedWidth::Int32 => ConditionTerm::signed_greater_equal(left, right),
            SignedDefinedWidth::Int64 => ConditionTerm::int64_signed_greater_equal(left, right),
        };
        let equal = |left, right| match width {
            SignedDefinedWidth::Int32 => ConditionTerm::equal(left, right),
            SignedDefinedWidth::Int64 => ConditionTerm::int64_equal(left, right),
        };
        let a = Bitvector32Term::Variable(Variable(94_001));
        let b = Bitvector32Term::Variable(Variable(94_002));
        let goal = Proposition::ConditionIs(
            match width {
                SignedDefinedWidth::Int32 => ConditionTerm::Overflows {
                    format: MachineIntegerType::Int32,
                    op: OverflowOperation::Add,
                    left: Box::new(a.clone()),
                    right: Box::new(b.clone()),
                },
                SignedDefinedWidth::Int64 => ConditionTerm::Overflows {
                    format: MachineIntegerType::Int64,
                    op: OverflowOperation::Add,
                    left: Box::new(a.clone()),
                    right: Box::new(b.clone()),
                },
            },
            false,
        );
        let mut works = Vec::new();
        for size in [8_u64, 16, 32, 64] {
            let mut assumptions = PureFactContext::new();
            for index in 0..size {
                let unrelated = Bitvector32Term::Variable(Variable(95_000 + index));
                let fact = match index % 3 {
                    0 => less(unrelated, constant(1_000)),
                    1 => at_least(unrelated, constant(-1_000)),
                    _ => equal(unrelated, constant(7)),
                };
                assumptions = assumptions.assume_condition(fact, true);
            }
            assumptions = assumptions
                .assume_condition(less(a.clone(), constant(100)), true)
                .assume_condition(at_least(a.clone(), constant(-5)), true)
                .assume_condition(equal(b.clone(), constant(1)), true);
            let (facts, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut facts = assumptions.signed_constant_bound_facts(width, &a);
                facts.extend(assumptions.signed_constant_bound_facts(width, &b));
                facts
            });
            assert_eq!(facts.len(), 3, "{width:?} at {size}: {facts:?}");
            let certificate = SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::SignedDefined {
                    width,
                    bounds: (0..facts.len()).collect(),
                    result: goal.clone(),
                }],
                conclusion: 0,
            };
            assert_eq!(certificate.check(&goal, &facts), Ok(()), "{width:?}");
            works.push(work);
        }
        assert!(
            works.iter().all(|work| *work == works[0]),
            "{width:?} bound selection work grew with unrelated bounds: {works:?}"
        );
    }
}

#[test]
fn equal_value_interval_queries_scale_with_delta_and_skip_unrelated_facts() {
    let mut works = Vec::new();
    for size in [32u64, 64, 128] {
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let root = Bitvector32Term::Variable(Variable(200_000 + size * 10));
            let mut facts = PureFactContext::new()
                .assume_condition(
                    ConditionTerm::signed_greater_equal(root.clone(), 0u32.into()),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_equal(root.clone(), 100u32.into()),
                    true,
                );
            PureFactContext::reset_signed_interval_fallback_fact_visits();
            for index in 0..size {
                let alias = Bitvector32Term::Variable(Variable(300_000 + size * 10 + index));
                let unrelated = Bitvector32Term::Variable(Variable(400_000 + size * 10 + index));
                facts = facts
                    .assume_condition(
                        ConditionTerm::signed_less_equal(unrelated, 1000u32.into()),
                        true,
                    )
                    .assume_condition(ConditionTerm::equal(root.clone(), alias.clone()), true);
                assert_eq!(facts.signed_interval(&alias), Some((0, 100)));
            }
            assert_eq!(PureFactContext::signed_interval_fallback_fact_visits(), 0);
        });
        assert!(work < 1000 * size as usize, "size={size}, work={work}");
        works.push(work);
    }
    assert!(
        works[2] < 6 * works[0],
        "interval lookup work grew too fast: {works:?}"
    );
}

/// An implicit order chain is not searched. An explicit endpoint bound
/// restores the interval without changing query cost as either component grows.
#[test]
fn order_chain_interval_requires_explicit_endpoint_bound() {
    let chain_context = |length: u64, unrelated: u64| {
        let mut assumptions = PureFactContext::new();
        for index in 0..unrelated {
            let a = Bitvector32Term::Variable(Variable(97_000 + 2 * index));
            let b = Bitvector32Term::Variable(Variable(97_001 + 2 * index));
            assumptions = assumptions
                .assume_condition(ConditionTerm::signed_less_equal(a, b.clone()), true)
                .assume_condition(
                    ConditionTerm::signed_less_than(b, Bitvector32Term::constant(50)),
                    true,
                );
        }
        let link = |index: u64| Bitvector32Term::Variable(Variable(98_000 + index));
        assumptions = assumptions.assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::constant(0), link(0)),
            true,
        );
        for index in 0..length {
            assumptions = assumptions.assume_condition(
                ConditionTerm::signed_less_equal(link(index), link(index + 1)),
                true,
            );
        }
        assumptions = assumptions.assume_condition(
            ConditionTerm::signed_less_than(link(length), Bitvector32Term::constant(1000)),
            true,
        );
        (assumptions, link(0))
    };
    let measure = |length: u64, unrelated: u64| {
        let (assumptions, start) = chain_context(length, unrelated);
        let (bound, work) = crate::instrumentation::measure_deterministic_work(|| {
            assumptions.signed_interval(&start)
        });
        assert_eq!(bound, Some((0, i64::from(i32::MAX))));
        let explicit = assumptions.assume_condition(
            ConditionTerm::signed_less_than(start.clone(), Bitvector32Term::constant(1000)),
            true,
        );
        let (bound, explicit_work) =
            crate::instrumentation::measure_deterministic_work(|| explicit.signed_interval(&start));
        assert_eq!(bound, Some((0, 999)));
        (work, explicit_work)
    };
    let samples = [8, 32, 128].map(|size| measure(size, size));
    assert!(
        samples
            .iter()
            .all(|work| work.0 <= samples[0].0 + 32 && work.1 <= samples[0].1 + 32),
        "{samples:?}"
    );
}

#[test]
fn int64_guard_work_is_independent_of_unrelated_facts() {
    let n = Bitvector32Term::Variable(Variable(95_111));
    let d = Bitvector32Term::Variable(Variable(95_112));
    let constant = Bitvector32Term::int64_constant;
    let mut work_counts = Vec::new();
    for size in [8, 32, 128, 512] {
        let mut facts = PureFactContext::new();
        for index in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::int64_signed_less_equal(
                    Bitvector32Term::Variable(Variable(96_000 + index)),
                    constant(123),
                ),
                true,
            );
        }
        facts = facts
            .assume_condition(ConditionTerm::int64_equal(n.clone(), constant(7)), true)
            .assume_condition(
                ConditionTerm::int64_signed_greater_than(d.clone(), constant(0)),
                true,
            );
        let (answers, work) = crate::instrumentation::measure_deterministic_work(|| {
            [
                facts.decide(&ConditionTerm::int64_signed_divide_overflows(
                    n.clone(),
                    d.clone(),
                )),
                facts.decide(&ConditionTerm::int64_signed_multiply_overflows(
                    n.clone(),
                    constant(2),
                )),
                facts.decide(&ConditionTerm::int64_signed_subtract_overflows(
                    n.clone(),
                    n.clone(),
                )),
            ]
        });
        assert_eq!(answers, [Some(false); 3]);
        work_counts.push(work);
    }
    assert!(
        work_counts.iter().all(|work| *work == work_counts[0]),
        "{work_counts:?}"
    );
    assert!(work_counts[0] > 0);
}

#[test]
fn int64_zero_alias_addition_and_subtraction_are_safe_and_indexed() {
    let x = Bitvector32Term::Variable(Variable(96_001));
    let zero = Bitvector32Term::Variable(Variable(96_002));
    let constant = Bitvector32Term::int64_constant;
    let mut baseline_work = None;
    for population in [8u64, 32, 128, 512] {
        let mut facts = PureFactContext::new()
            .assume_condition(ConditionTerm::int64_equal(zero.clone(), constant(0)), true);
        for i in 0..population {
            facts = facts.assume_condition(
                ConditionTerm::int64_signed_less_equal(
                    Bitvector32Term::Variable(Variable(97_000 + i)),
                    constant(100),
                ),
                true,
            );
        }
        let (answers, work) = crate::instrumentation::measure_deterministic_work(|| {
            [
                facts.decide(&ConditionTerm::int64_signed_add_overflows(
                    x.clone(),
                    zero.clone(),
                )),
                facts.decide(&ConditionTerm::int64_signed_add_overflows(
                    zero.clone(),
                    x.clone(),
                )),
                facts.decide(&ConditionTerm::int64_signed_subtract_overflows(
                    x.clone(),
                    zero.clone(),
                )),
                facts.decide(&ConditionTerm::int64_equal(
                    Bitvector32Term::int64_add(x.clone(), zero.clone()),
                    x.clone(),
                )),
                facts.decide(&ConditionTerm::int64_equal(
                    Bitvector32Term::int64_subtract(x.clone(), zero.clone()),
                    x.clone(),
                )),
            ]
        });
        assert_eq!(
            answers,
            [
                Some(false),
                Some(false),
                Some(false),
                Some(true),
                Some(true)
            ]
        );
        assert!(work > 0);
        assert_eq!(
            facts.decide(&ConditionTerm::int64_equal(
                Bitvector32Term::int64_add(x.clone(), constant(1)),
                x.clone()
            )),
            None
        );
        if let Some(baseline) = baseline_work {
            assert_eq!(work, baseline);
        } else {
            baseline_work = Some(work);
        }
        // An unknown nonzero addend/subtrahend can still overflow.
        assert_eq!(
            facts.decide(&ConditionTerm::int64_signed_add_overflows(
                x.clone(),
                constant(1)
            )),
            None
        );
        assert_eq!(
            facts.decide(&ConditionTerm::int64_signed_subtract_overflows(
                x.clone(),
                constant(1)
            )),
            None
        );
        assert_eq!(
            facts.decide(&ConditionTerm::int64_signed_subtract_overflows(
                zero.clone(),
                x.clone()
            )),
            None
        );
    }
    for edge in [i64::MIN, i64::MAX] {
        let facts = PureFactContext::new()
            .assume_condition(ConditionTerm::int64_equal(zero.clone(), constant(0)), true);
        assert_eq!(
            facts.decide(&ConditionTerm::int64_signed_add_overflows(
                constant(edge),
                zero.clone()
            )),
            Some(false)
        );
        assert_eq!(
            facts.decide(&ConditionTerm::int64_signed_subtract_overflows(
                constant(edge),
                zero.clone()
            )),
            Some(false)
        );
    }
}

#[test]
fn int64_zero_identity_chains_scale_with_the_queried_term() {
    let x = Bitvector32Term::Variable(Variable(98_001));
    let zero = Bitvector32Term::Variable(Variable(98_002));
    let facts = PureFactContext::new().assume_condition(
        ConditionTerm::int64_equal(zero.clone(), Bitvector32Term::int64_constant(0)),
        true,
    );
    let mut previous = None;
    for depth in [8usize, 32, 128, 512] {
        let mut term = x.clone();
        for _ in 0..depth {
            term = Bitvector32Term::int64_add(term, zero.clone());
        }
        let query = ConditionTerm::int64_equal(term, x.clone());
        let (answer, work) =
            crate::instrumentation::measure_deterministic_work(|| facts.decide(&query));
        assert_eq!(answer, Some(true));
        assert!(work > 0);
        if let Some((old_depth, old_work)) = previous {
            assert!(
                work <= old_work * depth / old_depth + 32,
                "{depth}: {work}, previous {old_work}"
            );
        }
        previous = Some((depth, work));
    }
}

#[test]
fn bit_preserving_64_bit_conversion_equalities_are_indexed_and_scale() {
    let value = Bitvector32Term::Variable(Variable(99_001));
    let mut baseline = None;
    for population in [8u64, 32, 128] {
        let mut facts = PureFactContext::new();
        for index in 0..population {
            facts = facts.assume_condition(
                ConditionTerm::uint64_equal(
                    Bitvector32Term::Variable(Variable(100_000 + index)),
                    Bitvector32Term::uint64_constant(0),
                ),
                true,
            );
        }
        let query = ConditionTerm::uint64_equal(
            Bitvector32Term::UInt64FromInt64(Box::new(value.clone())),
            value.clone(),
        );
        let (answer, work) =
            crate::instrumentation::measure_deterministic_work(|| facts.decide(&query));
        assert_eq!(answer, Some(true));
        if let Some(previous) = baseline {
            assert_eq!(work, previous);
        } else {
            baseline = Some(work);
        }
    }
    let facts = PureFactContext::new();
    let mut previous = None;
    for depth in [8usize, 32, 128, 512] {
        let mut term = value.clone();
        for _ in 0..depth {
            term = Bitvector32Term::UInt64FromInt64(Box::new(term));
        }
        let query = ConditionTerm::uint64_equal(term, value.clone());
        let (answer, work) =
            crate::instrumentation::measure_deterministic_work(|| facts.decide(&query));
        assert_eq!(answer, Some(true));
        if let Some((old_depth, old_work)) = previous {
            assert!(
                work <= old_work * depth / old_depth + 32,
                "{depth}: {work}, previous {old_work}"
            );
        }
        previous = Some((depth, work));
    }
}

#[test]
fn signed_wide_interval_queries_ignore_bound_bucket_size() {
    let mut baseline = None;
    for size in [4, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let x = Bitvector32Term::Variable(Variable(982002));
        let mut facts = PureFactContext::new();
        for offset in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::int64_signed_less_equal(
                    Bitvector32Term::int64_constant(-1000 - offset),
                    x.clone(),
                ),
                true,
            );
            facts = facts.assume_condition(
                ConditionTerm::int64_signed_less_equal(
                    x.clone(),
                    Bitvector32Term::int64_constant(1000 + offset),
                ),
                true,
            );
        }
        let (range, work) =
            crate::instrumentation::measure_deterministic_work(|| facts.int64_interval(&x));
        assert_eq!(range, Some((-1000, 1000)));
        if let Some(expected) = baseline {
            assert_eq!(work, expected, "size={size}");
        } else {
            baseline = Some(work);
        }
    }
}

#[test]
fn shared_masked_order_queries_do_not_export_growing_operands() {
    use crate::kernel::{
        IntegerTerm, KernelTerm, KernelTermImport, KernelType, SharedMachineIntegerTerm,
    };
    let mut samples = Vec::new();
    for size in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let mut root = KernelTerm::variable(KernelType::C(ty.c_type()), Variable(985302));
        let mask = KernelTermImport::default()
            .machine_arithmetic(ty, &Bitvector32Term::constant(127))
            .unwrap();
        let context = PureFactContext::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [root.clone(), root.clone()],
                );
                let masked = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::BitwiseAnd,
                    [root.clone(), mask.clone()],
                );
                let machine = SharedMachineIntegerTerm::from_shared(ty, masked).unwrap();
                for (bound, expected) in [(128, Some(true)), (0, Some(false)), (42, None)] {
                    let query = ConditionTerm::IntegerLessThan(
                        IntegerTerm::Machine(machine.clone()).into(),
                        IntegerTerm::constant(bound.into()).into(),
                    );
                    assert_eq!(context.decide_masked_order(&query), expected);
                    if expected.is_some() {
                        assert_eq!(context.decide(&query), expected);
                    }
                    assert!(!machine.has_boxed_operand());
                }
            }
        });
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small * 4 <= sw * large * 5, "{samples:?}");
    }
}

#[test]
fn shared_widened_queries_and_evidence_do_not_export_operands() {
    use crate::kernel::{
        IntegerTerm, KernelMachineCastEncoding as E, KernelTerm, KernelType,
        SharedMachineIntegerTerm,
    };
    let mut samples = Vec::new();
    for size in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut root = KernelTerm::variable(
            KernelType::C(MachineIntegerType::UInt32.c_type()),
            Variable(986201),
        );
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::UInt32,
                MachineBinaryOp::Add,
                [root.clone(), root.clone()],
            );
        }
        let operand =
            SharedMachineIntegerTerm::from_shared(MachineIntegerType::UInt32, root.clone())
                .unwrap();
        let widened = KernelTerm::machine_cast_shared(
            E::Int64FromUInt32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            root,
        );
        let sum = SharedMachineIntegerTerm::from_shared(
            MachineIntegerType::Int64,
            KernelTerm::machine_binary_shared(
                MachineIntegerType::Int64,
                MachineBinaryOp::Add,
                [widened.clone(), widened],
            ),
        )
        .unwrap();
        // Isolate comparison/evidence queries from ordinary fact admission,
        // whose native-comparison compatibility bridge is not yet migrated.
        let context = PureFactContext::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for (bound, expected) in [
                (2 * i64::from(u32::MAX), Some(true)),
                (2 * i64::from(u32::MAX) - 1, None),
                (-1, Some(false)),
            ] {
                let condition = ConditionTerm::IntegerLessEqual(
                    IntegerTerm::Machine(sum.clone()).into(),
                    IntegerTerm::constant(bound.into()).into(),
                );
                assert_eq!(context.decide_widened_sum_bound(&condition), expected);
                if expected.is_some() {
                    assert_eq!(context.decide(&condition), expected);
                }
                let sources = context
                    .widened_unsigned_sum_bound_premises(&condition)
                    .unwrap();
                assert!(sources.is_empty());
                if expected == Some(true) {
                    let (evidence, _) = context
                        .selected_for_test()
                        .proves_atomic_for_derivation_with_id(
                            &Proposition::ConditionIs(condition, true),
                            true,
                        );
                    assert!(matches!(evidence, Some(crate::kernel::AtomicPropositionDerivationEvidence::WidenedUnsignedSumBound)));
                }
                assert!(!sum.has_boxed_operand());
                assert!(!operand.has_boxed_operand());
            }
        });
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small * 4 <= sw * large * 5, "{samples:?}");
    }
}

#[test]
fn widened_source_selection_is_bounded_in_related_bounds() {
    let mut samples = Vec::new();
    for size in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let value = Bitvector32Term::Variable(Variable(986202));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(
                ConditionTerm::unsigned_less_equal(value.clone(), (100 + index as u32).into()),
                true,
            );
        }
        let sum = Bitvector32Term::int64_add(
            Bitvector32Term::int64_from_uint32(value.clone()),
            Bitvector32Term::int64_from_uint32(value),
        );
        let query =
            ConditionTerm::int64_signed_less_equal(sum, Bitvector32Term::int64_constant(200));
        let (sources, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.widened_unsigned_sum_bound_premises(&query).unwrap()
        });
        assert!(sources.len() <= 12);
        let selected = sources
            .into_iter()
            .fold(PureFactContext::new(), |context, source| {
                context.assume_proposition(source)
            });
        assert_eq!(selected.decide_widened_sum_bound(&query), Some(true));
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn indexed_lower_bound_decision_retains_shared_operands() {
    use crate::kernel::{
        IntegerTerm, KernelTerm, KernelType, MachineBinaryOp, SharedMachineIntegerTerm,
    };
    for size in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut root = KernelTerm::variable(
            KernelType::C(MachineIntegerType::Int32.c_type()),
            Variable(986302),
        );
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [root.clone(), root.clone()],
            );
        }
        let operand =
            SharedMachineIntegerTerm::from_shared(MachineIntegerType::Int32, root).unwrap();
        let observed = IntegerTerm::Machine(operand.clone());
        let lower = ConditionTerm::IntegerLessEqual(
            IntegerTerm::constant(3.into()).into(),
            observed.clone().into(),
        );
        let upper = ConditionTerm::IntegerLessEqual(
            observed.clone().into(),
            IntegerTerm::constant(7.into()).into(),
        );
        // Exercise the migrated index and dispatcher independently of the
        // full admission bridge, which still files a boxed compatibility fact.
        let mut facts = PureFactContext::new();
        facts.checked_order_bounds.adjust(&lower, true, true);
        facts.checked_order_bounds.adjust(&upper, true, true);
        for (value, expected) in [(2, Some(true)), (5, None), (8, Some(false))] {
            let query = ConditionTerm::IntegerGreaterEqual(
                observed.clone().into(),
                IntegerTerm::constant(value.into()).into(),
            );
            assert_eq!(facts.decide_indexed_greater_equal(&query), expected);
            if expected.is_some() {
                assert_eq!(facts.decide(&query), expected);
            }
            assert!(!operand.has_boxed_operand());
        }
    }
}

#[test]
fn signed_ranges_keep_shared_prefixes_and_memoize_refusals() {
    use crate::kernel::{KernelTerm, KernelType, MachineBinaryOp, SharedMachineIntegerTerm};
    let mut samples = Vec::new();
    for size in [8, 32, 96] {
        for ambient in [1, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let ty = MachineIntegerType::Int32;
            let x = Bitvector32Term::Variable(Variable(994601));
            let mut facts = PureFactContext::new()
                .assume_condition(
                    ConditionTerm::signed_less_equal(Bitvector32Term::constant(0), x.clone()),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_equal(x.clone(), Bitvector32Term::constant(1)),
                    true,
                );
            for i in 0..ambient {
                facts = facts.assume_condition(
                    ConditionTerm::equal(
                        Bitvector32Term::Variable(Variable(995600 + i)),
                        Bitvector32Term::constant(3),
                    ),
                    true,
                );
            }
            let mut root = KernelTerm::variable(KernelType::C(ty.c_type()), Variable(994601));
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                for level in 1..=size {
                    root = KernelTerm::machine_binary_shared(
                        ty,
                        MachineBinaryOp::Add,
                        [root.clone(), root.clone()],
                    );
                    let operand = SharedMachineIntegerTerm::from_shared(ty, root.clone()).unwrap();
                    let expected = if level < 31 {
                        Some((0, 1i64 << level))
                    } else {
                        None
                    };
                    assert_eq!(facts.signed_interval_view(operand.operand_view()), expected);
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
fn shared_overflow_queries_keep_prefixes_across_context_changes() {
    use crate::kernel::machine_integer::{Operation, definedness};
    use crate::kernel::{KernelTerm, KernelType, SharedMachineIntegerTerm};
    let mut samples = Vec::new();
    // Cross the 32-bit wrap threshold while keeping admission in the fast gate.
    for size in [4, 12, 36] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut root = KernelTerm::variable(KernelType::C(format.c_type()), Variable(996701));
        let mut context = PureFactContext::new();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [root.clone(), root.clone()],
                );
                let operand = SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap();
                let observed = IntegerTerm::Machine(operand.clone());
                let exact = Operation::Add.exact(observed.clone(), IntegerTerm::constant(2.into()));
                let query = definedness::overflow_query_of_integer_bound(
                    &definedness::ordinary_bounds(format, exact)[0],
                    std::iter::once(format),
                )
                .unwrap();
                // File the bounds normally, so their context identity and
                // interval memoization are the ones used during proof steps.
                context = context
                    .assume_condition(
                        ConditionTerm::IntegerLessEqual(
                            IntegerTerm::constant(0.into()).into(),
                            observed.clone().into(),
                        ),
                        true,
                    )
                    .assume_condition(
                        ConditionTerm::IntegerLessEqual(
                            observed.into(),
                            IntegerTerm::constant(10.into()).into(),
                        ),
                        true,
                    );
                assert_eq!(
                    context.decide_overflow_query(&query),
                    Some(false),
                    "prefix {index}"
                );
                context = context.clone().assume_condition(
                    ConditionTerm::equal(
                        Bitvector32Term::Variable(Variable(996800 + index)),
                        Bitvector32Term::constant(3),
                    ),
                    true,
                );
                assert_eq!(context.decide_overflow_query(&query), Some(false));
                assert!(!operand.has_boxed_operand());
            }
        });
        samples.push((size as usize, work));
    }
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small <= sw * large * 2, "{samples:?}");
    }
}

#[test]
fn retained_overflow_source_lookup_ignores_unrelated_guards() {
    use crate::kernel::machine_integer::{Operation, definedness};
    use crate::kernel::{KernelTermImport, SharedMachineIntegerTerm};
    let mut samples = Vec::new();
    for size in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let written = Bitvector32Term::Variable(Variable(997701));
        let operand = SharedMachineIntegerTerm::from_shared(
            format,
            KernelTermImport::default()
                .machine_arithmetic(format, &written)
                .unwrap(),
        )
        .unwrap();
        let source = Proposition::ConditionIs(
            ConditionTerm::Overflows {
                format,
                op: OverflowOperation::Multiply,
                left: written.into(),
                right: Bitvector32Term::constant(2).into(),
            },
            false,
        );
        let mut context = PureFactContext::new().assume_proposition(source.clone());
        for i in 0..size {
            context = context.assume_condition(
                ConditionTerm::Overflows {
                    format,
                    op: OverflowOperation::Multiply,
                    left: Bitvector32Term::Variable(Variable(997800 + i)).into(),
                    right: Bitvector32Term::constant(2).into(),
                },
                false,
            );
        }
        let exact = Operation::Multiply.exact(
            IntegerTerm::Machine(operand.clone()),
            IntegerTerm::constant(2.into()),
        );
        let query = definedness::overflow_query_of_integer_bound(
            &definedness::ordinary_bounds(format, exact)[0],
            std::iter::once(format),
        )
        .unwrap();
        let (answer, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.contains_known_overflow_query(&query, false)
        });
        assert!(answer);
        assert_eq!(context.stated_overflow_source(&query, false), Some(&source));
        assert!(!operand.has_boxed_operand());
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}
