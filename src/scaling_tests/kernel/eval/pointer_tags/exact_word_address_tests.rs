// Scaling tests of `src/kernel/eval/pointer_tags.rs` (module `exact_word_address_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::{MachineCastSpelling, MachineTerm};

#[test]
fn object_class_origin_lookup_is_independent_of_unrelated_facts() {
    use crate::kernel::effective_type::{CAccessClass, CScalarClass};
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Pointer::symbolic(Variable(960010));
    let class = CAccessClass::Scalar(CScalarClass::Int);
    let word = MachineTerm::Variable(Variable(960011));
    let premise = ConditionTerm::uint64_equal(
        word.clone(),
        MachineTerm::object_pointer_address(pointer.clone(), Some(class.clone())),
    );
    let mut costs = Vec::new();
    for size in [4, 16, 64, 256] {
        let mut context = PureFactContext::new().assume_condition(premise.clone(), true);
        for index in 0..size {
            context = context.assume_condition(
                ConditionTerm::uint64_equal(
                    MachineTerm::Variable(Variable(970000 + index)),
                    MachineTerm::uint64_constant(index),
                ),
                true,
            );
        }
        let mut obligations = Vec::new();
        let (decoded, work) = crate::instrumentation::measure_deterministic_work(|| {
            cast_tagged_address_to_pointer(
                &word,
                &context,
                &mut obligations,
                ProgramType::Float64Pointer,
            )
        });
        let decoded = decoded.unwrap().unwrap();
        assert_eq!(decoded.pointer(), &pointer);
        assert_eq!(decoded.object_class(), Some(class.clone()));
        assert!(obligations.is_empty());
        costs.push(work);
    }
    assert!(
        costs[0] > 0 && costs.iter().all(|cost| *cost <= costs[0] * 2),
        "{costs:?}"
    );
}

// A compound word's exact address is an indexed premise. Unrelated word
// equalities must neither be searched nor create conversion obligations.
#[test]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn compound_word_address_lookup_skips_unrelated_equalities() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Pointer::symbolic(Variable(960001));
    let word = MachineTerm::Variable(Variable(960002));
    let expressions = [
        MachineTerm::uint64_bitwise_and(word.clone(), MachineTerm::uint64_constant(!3)),
        MachineTerm::uint64_bitwise_or(word, MachineTerm::Variable(Variable(960003))),
    ];
    for expression in expressions {
        let fact = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                expression.clone(),
                MachineTerm::PointerAddress(
                    Box::new(pointer.clone()),
                    crate::kernel::AddressObjectClass::NONE,
                ),
            ),
            true,
        );
        let mut costs = Vec::new();
        for size in [16, 64, 256, 1024] {
            let mut assumptions = PureFactContext::new().assume_proposition(fact.clone());
            for index in 0..size {
                assumptions = assumptions.assume_condition(
                    ConditionTerm::uint64_equal(
                        MachineTerm::Variable(Variable(970000 + index)),
                        MachineTerm::uint64_constant(index),
                    ),
                    true,
                );
            }
            let mut used = UsedFacts::new();
            let (form, work) = crate::instrumentation::measure_deterministic_work(|| {
                tagged_address_form(&expression, &assumptions, &mut used)
            });
            let form = form.expect("the exact address equation names the original pointer");
            assert_eq!(form.pointer, pointer);
            assert_eq!(form.tag.operand_view().uint64_constant(), Some(0));
            assert!(used.complete);
            assert_eq!(used.premises, vec![fact.clone()]);
            let mut obligations = Vec::new();
            assert_eq!(
                cast_tagged_address_to_pointer(
                    &expression,
                    &assumptions,
                    &mut obligations,
                    ProgramType::Int32Pointer
                )
                .unwrap()
                .map(|value| value.pointer().clone()),
                Some(pointer.clone())
            );
            assert!(obligations.is_empty());
            costs.push(work);
        }
        assert!(
            costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] * 2),
            "{costs:?}"
        );
    }
}

#[test]
fn bounded_symbolic_tag_lookup_ignores_unrelated_facts() {
    let costs = [4u64, 16, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let tag = MachineTerm::Variable(Variable(980_021));
        let pointer = Pointer::symbolic(Variable(980_022));
        let mut context = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_equal(0u32.into(), tag.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(tag.clone(), 1u32.into()),
                true,
            )
            .assume_condition(ConditionTerm::pointer_aligned(pointer.clone(), 8), true);
        for index in 0..size {
            context = context.assume_condition(
                ConditionTerm::uint64_equal(
                    MachineTerm::Variable(Variable(990_000 + index)),
                    MachineTerm::uint64_constant(index),
                ),
                true,
            );
        }
        let cleared = MachineTerm::uint64_bitwise_and(
            MachineTerm::uint64_bitwise_or(
                MachineTerm::pointer_address(pointer.clone()),
                MachineTerm::legacy_cast(MachineCastSpelling::UInt64FromInt32, Box::new(tag)),
            ),
            MachineTerm::uint64_constant(!3),
        );
        let (form, work) = crate::instrumentation::measure_deterministic_work(|| {
            tagged_address_form(&cleared, &context, &mut UsedFacts::new())
        });
        assert_eq!(form.unwrap().pointer, pointer);
        work
    });
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] + 32),
        "{costs:?}"
    );
}

#[test]
fn shared_tag_bounds_reuse_growing_dags_across_contexts() {
    use crate::kernel::{KernelTerm, KernelTermExport, KernelTermImport};
    let mut samples = Vec::new();
    for size in [32, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::UInt64;
        let mut root = KernelTermImport::default()
            .machine_arithmetic(
                ty,
                &MachineTerm::uint64_bitwise_and(
                    MachineTerm::Variable(Variable(985311)),
                    MachineTerm::uint64_constant(3),
                ),
            )
            .unwrap();
        let mut context = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                context = context
                    .clone()
                    .assume_condition(ConditionTerm::Variable(Variable(985400 + index)), true);
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::BitwiseOr,
                    [root.clone(), root],
                );
                assert_eq!(tag_bound(MachineOperandView::Shared(&root)), Some(3));
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|p| p[1] <= p[0] * 5 + 100),
        "{samples:?}"
    );
}

#[test]
fn unknown_left_tag_bound_does_not_visit_the_right_dag() {
    use crate::kernel::{KernelTerm, KernelTermExport, KernelTermImport};
    let mut samples = Vec::new();
    for size in [8, 64, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::UInt64;
        let unknown = KernelTermImport::default()
            .machine_arithmetic(ty, &MachineTerm::Variable(Variable(985312)))
            .unwrap();
        let mut right = KernelTermImport::default()
            .machine_arithmetic(ty, &MachineTerm::uint64_constant(3))
            .unwrap();
        for _ in 0..size {
            right = KernelTerm::machine_binary_shared(
                ty,
                MachineBinaryOp::BitwiseOr,
                [right.clone(), right],
            );
        }
        let root =
            KernelTerm::machine_binary_shared(ty, MachineBinaryOp::BitwiseOr, [unknown, right]);
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(tag_bound(MachineOperandView::Shared(&root)), None);
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn cited_shared_tag_bounds_retain_growing_prefixes_and_selected_sources() {
    use crate::kernel::machine_integer::comparison::condition_for_operand_views;
    use crate::kernel::{KernelTerm, KernelTermExport, KernelTermImport};
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::UInt32;
        let mut root = KernelTermImport::default()
            .machine_arithmetic(ty, &MachineTerm::Variable(Variable(985331)))
            .unwrap();
        let one = KernelTermImport::default()
            .machine_arithmetic(ty, &MachineTerm::constant(1))
            .unwrap();
        let mut context = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Multiply,
                    [root, one.clone()],
                );
                let converted = KernelTerm::machine_cast_shared(
                    MachineCastSpelling::UInt64From32,
                    ty,
                    MachineIntegerType::UInt64,
                    root.clone(),
                );
                assert_eq!(
                    tag_bound_citing(
                        MachineOperandView::Shared(&converted),
                        &context,
                        &mut UsedFacts::new()
                    ),
                    None
                );
                let upper = condition_for_operand_views(
                    ty,
                    CompareRelation::LessEqual,
                    [
                        MachineOperandView::Shared(&root),
                        MachineOperandView::Legacy(&MachineTerm::constant(3)),
                    ],
                );
                context = context.clone().assume_condition(upper.clone(), true);
                let mut used = UsedFacts::new();
                assert_eq!(
                    tag_bound_citing(MachineOperandView::Shared(&converted), &context, &mut used),
                    Some(3)
                );
                assert!(
                    used.premises
                        .contains(&Proposition::ConditionIs(upper, true))
                );
                assert!(used.complete);
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|p| p[1] <= p[0] * 5 + 100),
        "{samples:?}"
    );
}

#[test]
fn retained_tag_forms_visit_shared_nodes_once_and_reuse_prefixes() {
    use crate::kernel::{KernelTerm, KernelTermExport, KernelTermImport};
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::UInt64;
        let x = MachineTerm::Variable(Variable(986020));
        // Keep a pointer source present, but unrelated: a missing root must
        // traverse its DAG once, not once per occurrence of a shared child.
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::uint64_equal(
                MachineTerm::Variable(Variable(986021)),
                MachineTerm::pointer_address(Pointer::symbolic(Variable(986022))),
            ),
            true,
        );
        let mut root = KernelTermImport::default()
            .machine_arithmetic(ty, &x)
            .unwrap();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [root.clone(), root],
                );
                assert!(
                    tagged_address_form_view(
                        MachineOperandView::Shared(&root),
                        &context,
                        &mut UsedFacts::new()
                    )
                    .is_none()
                );
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples[0] > 0 && samples.windows(2).all(|p| p[1] <= p[0] * 5 + 100),
        "{samples:?}"
    );
}

#[test]
fn mixed_tag_syntax_comparison_reuses_growing_shared_prefixes() {
    use crate::kernel::{KernelTerm, KernelTermExport, SharedMachineIntegerTerm};
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::UInt64;
        let opaque = MachineTerm::pointer_address(Pointer::symbolic(Variable(986050)));
        let mut left =
            KernelTerm::retained_machine_operand(ty, MachineOperandView::Legacy(&opaque));
        let mut right =
            KernelTerm::retained_machine_operand(ty, MachineOperandView::Legacy(&opaque));
        assert_ne!(left, right);
        let one = KernelTerm::retained_machine_operand(
            ty,
            MachineOperandView::Legacy(&MachineTerm::uint64_constant(1)),
        );
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                left = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [left, one.clone()],
                );
                right = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [right, one.clone()],
                );
                assert!(same_tag_syntax(
                    &SharedMachineIntegerTerm::from_shared(ty, left.clone()).unwrap(),
                    &SharedMachineIntegerTerm::from_shared(ty, right.clone()).unwrap()
                ));
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples[0] > 0 && samples.windows(2).all(|p| p[1] <= p[0] * 5 + 100),
        "{samples:?}"
    );
}
