use super::*;
use crate::kernel::binary_node;
fn var(id: u64) -> OldMachineTerm {
    OldMachineTerm::Variable(Variable(id))
}
fn add(left: OldMachineTerm, right: OldMachineTerm) -> OldMachineTerm {
    binary_node!(Int32, Add, Box::new(left), Box::new(right))
}
fn eq(left: OldMachineTerm, right: OldMachineTerm) -> OldConditionTerm {
    OldConditionTerm::equal(left, right)
}

#[test]
fn int32_addition_closes_both_operands_early_and_late_through_scaled_offsets() {
    for early in [false, true] {
        let mut graph = EqualityGraph::default();
        if early {
            graph.add_int32_equality(&var(1), &var(2));
        }
        let left = add(add(var(1), var(3)), var(5));
        let right = add(add(var(2), var(4)), var(5));
        graph.add_int32_equality(&left, &var(10));
        graph.add_int32_equality(&right, &var(11));
        let offset = |v| OldAddressOffset::scale_int32(v, 4);
        let alias = |i| OldAddressOffset::Variable(Variable(i));
        graph.add_offset_equality(
            &crate::kernel::AddressOffset::from(&offset(left)),
            &crate::kernel::AddressOffset::from(&alias(20)),
        );
        graph.add_offset_equality(
            &crate::kernel::AddressOffset::from(&offset(right)),
            &crate::kernel::AddressOffset::from(&alias(21)),
        );
        let parent = graph.clone();
        let sibling = graph.clone();
        if !early {
            graph.add_int32_equality(&var(1), &var(2));
        }
        assert!(!graph.are_int32_equal(&var(10), &var(11)));
        graph.add_int32_equality(&var(4), &var(3));
        assert!(graph.are_int32_equal(&var(11), &var(10)));
        assert!(graph.are_offsets_equal(
            &crate::kernel::AddressOffset::from(&alias(20)),
            &crate::kernel::AddressOffset::from(&alias(21))
        ));
        for unchanged in [parent, sibling] {
            assert!(!unchanged.are_int32_equal(&var(10), &var(11)));
            assert!(!unchanged.are_offsets_equal(
                &crate::kernel::AddressOffset::from(&alias(20)),
                &crate::kernel::AddressOffset::from(&alias(21))
            ));
        }
    }
}

#[test]
fn int32_addition_folds_literal_classes_using_bitvector_semantics() {
    for (a, b) in [(1u32, 2u32), (u32::MAX, 1), (i32::MAX as u32, 1)] {
        for early in [false, true] {
            let mut graph = EqualityGraph::default();
            if early {
                graph.add_int32_equality(&var(1), &OldMachineTerm::constant(a));
                graph.add_int32_equality(&var(2), &OldMachineTerm::constant(b));
            }
            graph.add_int32_equality(&add(var(1), var(2)), &var(10));
            if !early {
                graph.add_int32_equality(&OldMachineTerm::constant(a), &var(1));
                graph.add_int32_equality(&OldMachineTerm::constant(b), &var(2));
            }
            let result = OldMachineTerm::constant(a.wrapping_add(b));
            assert!(graph.are_int32_equal(&var(10), &result));
            assert!(graph.are_int32_equal(
                &add(OldMachineTerm::constant(a), OldMachineTerm::constant(b)),
                &result
            ));
            assert!(!graph.are_int32_equal(
                &var(10),
                &OldMachineTerm::constant(a.wrapping_add(b).wrapping_add(1))
            ));
        }
    }
}

#[test]
fn int32_addition_does_not_cancel_commute_or_merge_other_sorts() {
    let mut graph = EqualityGraph::default();
    graph.add_int32_equality(&add(var(1), var(3)), &add(var(2), var(3)));
    assert!(!graph.are_int32_equal(&var(1), &var(2)));
    assert!(!graph.are_int32_equal(&add(var(1), var(3)), &add(var(3), var(1))));
    graph.add_int32_equality(&var(1), &var(2));
    let wide = |v| OldMachineTerm::Binary {
        format: MachineIntegerType::Int64,
        op: MachineBinaryOp::Add,
        left: Box::new(v),
        right: Box::new(var(3)),
    };
    assert!(!graph.are_int32_equal(&wide(var(1)), &wide(var(2))));
    assert!(!graph.are_int32_equal(&add(var(1), var(3)), &wide(var(1))));
    let scalar_offset = OldAddressOffset::scale_int32(add(var(1), var(3)), 4);
    let offset_sum = OldAddressOffset::Add(
        Box::new(OldAddressOffset::Variable(Variable(1))),
        Box::new(OldAddressOffset::Variable(Variable(3))),
    );
    assert!(!graph.are_offsets_equal(
        &crate::kernel::AddressOffset::from(&scalar_offset),
        &crate::kernel::AddressOffset::from(&offset_sum)
    ));
}

#[test]
fn int32_addition_restriction_preserves_only_supported_equalities() {
    let premise = eq(var(1), var(2));
    let explicit = eq(add(var(2), var(3)), var(10));
    let context = PureFactContext::new()
        .assume_condition(premise.clone(), true)
        .assume_condition(explicit.clone(), true);
    let query = add(var(1), var(3));
    assert!(context.equality_graph.are_int32_equal(&query, &var(10)));
    let restricted = context.restricted_to_facts(&[(premise, true)], &[]);
    assert!(
        restricted
            .equality_graph
            .are_int32_equal(&query, &add(var(2), var(3)))
    );
    assert!(!restricted.equality_graph.are_int32_equal(&query, &var(10)));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/int32_addition_tests.rs");
}
