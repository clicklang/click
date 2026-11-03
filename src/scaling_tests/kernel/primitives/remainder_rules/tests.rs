// Scaling tests of `src/kernel/primitives/remainder_rules.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::binary_node;

#[test]
fn uint64_small_remainder_requires_the_strict_full_width_guard() {
    let n = B::Variable(Variable(120));
    let d = B::Variable(Variable(121));
    let input = B::uint64_remainder(n.clone(), d.clone());
    let guard = C::uint64_less_than(n.clone(), d.clone());
    for facts in [
        HashMap::new(),
        HashMap::from([(guard.clone(), false)]),
        HashMap::from([(C::uint64_less_equal(n.clone(), d.clone()), true)]),
        HashMap::from([(C::signed_less_than(n.clone(), d.clone()), true)]),
    ] {
        assert_eq!(TermRewrite::for_conditions(&facts).bits(&input), input);
    }
    let mut measured = Vec::new();
    for count in [0, 32, 128, 512] {
        let mut facts = HashMap::from([(guard.clone(), true)]);
        for i in 0..count {
            facts.insert(
                C::equal(B::Variable(Variable(2000 + i)), B::Constant(i as u32)),
                true,
            );
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            TermRewrite::for_conditions(&facts).bits(&input)
        });
        assert_eq!(result, n);
        measured.push(work);
    }
    assert!(
        measured.iter().all(|work| *work == measured[0]),
        "{measured:?}"
    );
    // The identity includes dividends above the signed high bit and
    // never treats a zero divisor or equality as the strict guard.
    for dividend in [0, 1, u32::MAX as u64, 1 << 63, u64::MAX - 1, u64::MAX] {
        for divisor in [0, 1, 4, (u32::MAX as u64) + 1, 1 << 63, u64::MAX] {
            if dividend < divisor {
                assert_eq!(dividend % divisor, dividend);
            }
        }
    }
}

#[test]
fn division_bound_lookup_ignores_unrelated_conditions() {
    let n = B::Variable(Variable(100));
    let d = B::Variable(Variable(101));
    let goal = C::signed_less_equal(
        binary_node!(UInt32, Divide, Box::new(n), Box::new(d)),
        B::Constant(65535),
    );
    let mut measured = Vec::new();
    for count in [0, 32, 128, 512] {
        let mut facts: HashMap<_, _> = goal
            .nonnegative_division_bound_guards()
            .unwrap()
            .into_iter()
            .map(|guard| (guard, true))
            .collect();
        for i in 0..count {
            facts.insert(
                C::equal(B::Variable(Variable(1000 + i)), B::Constant(i as u32)),
                true,
            );
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            TermRewrite::for_conditions(&facts).condition(&goal)
        });
        assert_eq!(result, C::Constant(true));
        measured.push(work);
    }
    assert!(
        measured.iter().all(|work| *work == measured[0]),
        "{measured:?}"
    );
}

#[test]
fn division_bound_work_scales_with_its_selected_expression() {
    let mut measured = Vec::new();
    for count in [16, 32, 64, 128] {
        let mut n = B::Variable(Variable(100));
        for i in 0..count {
            n = binary_node!(
                Int32,
                Add,
                Box::new(n),
                Box::new(B::Variable(Variable(1000 + i)))
            );
        }
        let goal = C::signed_less_equal(
            binary_node!(
                UInt32,
                Divide,
                Box::new(n),
                Box::new(B::Variable(Variable(101)))
            ),
            B::Constant(65535),
        );
        let facts: HashMap<_, _> = goal
            .nonnegative_division_bound_guards()
            .unwrap()
            .into_iter()
            .map(|guard| (guard, true))
            .collect();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            TermRewrite::for_conditions(&facts).condition(&goal)
        });
        assert_eq!(result, C::Constant(true));
        measured.push(work);
    }
    assert!(
        measured.windows(2).all(|pair| pair[1] <= 3 * pair[0]),
        "{measured:?}"
    );
}

#[test]
fn remainder_guard_lookup_ignores_unrelated_conditions() {
    let n = B::Variable(Variable(100));
    let input = B::remainder(B::subtract(n.clone(), B::Constant(4)), B::Constant(4));
    let guard = C::signed_less_equal(B::Constant(4), n.clone());
    let mut measured = Vec::new();
    for count in [0, 32, 128, 512] {
        let mut facts = HashMap::from([(guard.clone(), true)]);
        for i in 0..count {
            facts.insert(
                C::equal(B::Variable(Variable(1000 + i)), B::Constant(i as u32)),
                true,
            );
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            TermRewrite::for_conditions(&facts).bits(&input)
        });
        assert_eq!(result, B::remainder(n.clone(), B::Constant(4)));
        measured.push(work);
    }
    assert!(
        measured.iter().all(|work| *work == measured[0]),
        "{measured:?}"
    );
}

#[test]
fn division_guards_retain_shared_prefixes_in_linear_work() {
    use crate::kernel::machine_integer::comparison::condition_for_operand_views;
    use crate::kernel::{CType, KernelTerm, KernelTermExport, KernelType, MachineOperandView as V};
    let samples = [16usize, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut n = KernelTerm::variable(KernelType::C(CType::Int32), Variable(990201));
        let d = KernelTerm::variable(KernelType::C(CType::Int32), Variable(990202));
        let zero = B::Constant(0);
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                n = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [n.clone(), n.clone()],
                );
                let q = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Divide,
                    [n.clone(), d.clone()],
                );
                for (relation, expected) in [
                    (CompareRelation::LessEqual, true),
                    (CompareRelation::LessThan, false),
                ] {
                    let query = condition_for_operand_views(
                        format,
                        relation,
                        [V::Legacy(&zero), V::Shared(&q)],
                    );
                    assert_eq!(
                        query.nonnegative_division_bound_guards().is_some(),
                        expected
                    );
                }
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        (size, work)
    });
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small <= sw * large * 2, "{samples:?}");
    }
}

#[test]
fn division_guard_casts_reuse_growing_composition_prefixes() {
    use crate::kernel::machine_integer::comparison::condition_for_operand_views;
    use crate::kernel::{
        CType, KernelMachineCastEncoding as Encoding, KernelTerm, KernelTermExport, KernelType,
        MachineOperandView as V,
    };
    let samples = [16usize, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let unsigned = MachineIntegerType::UInt32;
        let signed = MachineIntegerType::Int32;
        let mut n = KernelTerm::variable(KernelType::C(CType::UInt32), Variable(990211));
        let d = KernelTerm::variable(KernelType::C(CType::UInt32), Variable(990212));
        let zero = B::Constant(0);
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                n = KernelTerm::machine_cast_shared(
                    Encoding::Generic,
                    unsigned,
                    unsigned,
                    n.clone(),
                );
                let q = KernelTerm::machine_binary_shared(
                    unsigned,
                    MachineBinaryOp::Divide,
                    [n.clone(), d.clone()],
                );
                let q = KernelTerm::machine_cast_shared(Encoding::Generic, unsigned, signed, q);
                let query = condition_for_operand_views(
                    signed,
                    CompareRelation::LessEqual,
                    [V::Legacy(&zero), V::Shared(&q)],
                );
                assert_eq!(query.nonnegative_division_bound_guards().unwrap().len(), 2);
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        (size, work)
    });
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small <= sw * large * 2, "{samples:?}");
    }
}
