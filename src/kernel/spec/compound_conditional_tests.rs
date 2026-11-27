use super::*;

#[test]
fn compound_guards_select_exact_values_and_keep_unknowns_undecided() {
    let a = OldConditionTerm::Variable(Variable(701));
    let b = OldConditionTerm::Variable(Variable(702));
    for conjunction in [false, true] {
        let left = Box::new(Proposition::condition_is(a.clone(), true));
        let right = Box::new(Proposition::condition_is(b.clone(), false));
        let guard = if conjunction {
            Proposition::And(left, right)
        } else {
            Proposition::Or(left, right)
        };
        let value = conditional_spec_value(&guard, int32(7), int32(9)).unwrap();
        let retained = SpecValue::conditional(&guard, &int32(7).into(), &int32(9).into(), true)
            .unwrap()
            .unwrap();
        assert_eq!(retained.into_native(), value);
        let ProgramValue::Int32(bits) = value else {
            panic!("int32 conditional");
        };
        let is_seven = OldConditionTerm::equal(bits, OldMachineTerm::constant(7));
        assert_eq!(PureFactContext::new().decide(&is_seven), None);
        for left in [false, true] {
            for right in [false, true] {
                let facts = PureFactContext::new()
                    .assume_proposition(Proposition::condition_is(a.clone(), left))
                    .assume_proposition(Proposition::condition_is(b.clone(), right));
                let expected = if conjunction {
                    left && !right
                } else {
                    left || !right
                };
                assert_eq!(facts.decide(&is_seven), Some(expected));
            }
        }
    }
}

#[test]
fn compound_guard_preserves_shared_predicates_and_written_word_selection() {
    let _session = crate::kernel::VerificationSession::enter();
    let format = KernelFloatType::Float64;
    let guard = |name: &str| {
        let operand = KernelTerm::float_call(format, name.into(), vec![]);
        KernelTerm::float_classify(format, FloatClassification::Zero, operand).unwrap()
    };
    let left = guard("compound_left");
    let right = guard("compound_right");
    let claim = |root: &KernelTerm, truth| {
        Box::new(Proposition::condition_is(
            StoredConditionTerm::from_root(root.clone()).unwrap(),
            truth,
        ))
    };
    let exports = KernelTermExport::float_export_count();
    for conjunction in [true, false] {
        for left_truth in [true, false] {
            for right_truth in [true, false] {
                let a = claim(&left, left_truth);
                let b = claim(&right, right_truth);
                let proposition = if conjunction {
                    Proposition::And(a, b)
                } else {
                    Proposition::Or(a, b)
                };
                let (guard, truth) = conditional_guard(&proposition).unwrap();
                assert!(truth);
                let word = |bit: bool| KernelTerm::int32_literal(u32::from(bit));
                let format = MachineIntegerType::Int32;
                let nested = KernelTerm::machine_if_shared(
                    format,
                    [right.clone(), word(right_truth), word(!right_truth)],
                );
                let shortcut = word(!conjunction);
                let arms = if left_truth == conjunction {
                    [left.clone(), nested, shortcut]
                } else {
                    [left.clone(), shortcut, nested]
                };
                let expected = KernelTerm::boolean_comparison_raw(
                    format,
                    CompareRelation::Equal,
                    [KernelTerm::machine_if_shared(format, arms), word(true)],
                );
                assert_eq!(guard.root(), Some(&expected));
            }
        }
    }
    assert_eq!(KernelTermExport::float_export_count(), exports);
    assert!(!left.has_cached_native_argument());
    assert!(!right.has_cached_native_argument());
}

#[test]
fn algebraic_equality_guard_keeps_its_operands_and_polarity() {
    let _session = crate::kernel::VerificationSession::enter();
    let native = KernelMatch::test_scrutinee(vec![]);
    let left =
        KernelTerm::algebraic_call(native.algebraic_type.clone(), "guard_left".into(), vec![]);
    let right = KernelTermImport::for_exact_field_inputs().algebraic(&native);
    let exports = KernelTermExport::algebraic_export_count();
    for right_term in [
        algebraic_output(right.clone()),
        Term::Algebraic(native.clone().into()),
    ] {
        let claim = Proposition::Not(Box::new(Proposition::Equal(
            algebraic_output(left.clone()),
            right_term,
        )));
        let (guard, expected) = conditional_guard(&claim).unwrap();
        assert!(!expected);
        let KernelTermNode::AlgebraicEqual { arguments } = guard.root().unwrap().node() else {
            panic!("expected algebraic equality")
        };
        assert_eq!(arguments, &[left.clone(), right.clone()]);
    }
    assert_eq!(KernelTermExport::algebraic_export_count(), exports);
    assert!(!left.has_cached_native_argument());
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/spec/compound_conditional_tests.rs");
}
