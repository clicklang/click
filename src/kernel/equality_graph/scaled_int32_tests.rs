use super::*;

fn scalar(id: u64) -> MachineTerm {
    MachineTerm::Variable(Variable(id))
}
fn offset(id: u64) -> PointerOffsetTerm {
    PointerOffsetTerm::Variable(Variable(id))
}
fn scaled(id: u64, width: i64) -> PointerOffsetTerm {
    PointerOffsetTerm::scale_int32(scalar(id), width)
}
fn nested(term: PointerOffsetTerm) -> PointerOffsetTerm {
    PointerOffsetTerm::Add(Box::new(term), Box::new(offset(90)))
}

#[test]
fn scaled_int32_congruence_propagates_early_and_late_into_addition_aliases() {
    for early in [false, true] {
        let mut graph = EqualityGraph::default();
        if early {
            graph.add_int32_equality(&scalar(1), &scalar(2));
        }
        graph.add_offset_equality(&nested(scaled(1, 4)), &offset(10));
        graph.add_offset_equality(&nested(scaled(3, 4)), &offset(11));
        let parent = graph.clone();
        let sibling = graph.clone();
        if !early {
            graph.add_int32_equality(&scalar(1), &scalar(2));
        }
        assert!(!graph.are_offsets_equal(&offset(10), &offset(11)));
        graph.add_int32_equality(&scalar(3), &scalar(2));
        assert!(graph.are_offsets_equal(&offset(11), &offset(10)));
        assert!(!parent.are_offsets_equal(&offset(10), &offset(11)));
        assert!(!sibling.are_offsets_equal(&offset(10), &offset(11)));
        assert!(!graph.are_offsets_equal(&scaled(1, 4), &scaled(3, 8)));
        for unsigned in [false, true] {
            let wide = |id| PointerOffsetTerm::scaled_int64_node(scalar(id), 4, unsigned);
            assert!(!graph.are_offsets_equal(&scaled(1, 4), &wide(1)));
            assert!(!graph.are_offsets_equal(&wide(1), &wide(3)));
        }
    }
    let mut graph = EqualityGraph::default();
    graph.add_offset_equality(&scaled(1, 4), &scaled(2, 4));
    assert!(!graph.are_int32_equal(&scalar(1), &scalar(2)));
}

#[test]
fn scaled_int32_literals_join_folded_constants_without_overflow() {
    for value in [0, 1, u32::MAX, i32::MIN as u32] {
        for early in [false, true] {
            let mut graph = EqualityGraph::default();
            let literal = MachineTerm::constant(value);
            if early {
                graph.add_int32_equality(&scalar(1), &literal);
            }
            graph.add_offset_equality(&nested(scaled(1, 4)), &offset(10));
            if !early {
                graph.add_int32_equality(&literal, &scalar(1));
            }
            let folded = PointerOffsetTerm::scale_int32(literal.clone(), 4);
            assert!(graph.are_offsets_equal(&offset(10), &nested(folded.clone())));
            let explicit = PointerOffsetTerm::scaled_int32_node(literal, 4);
            assert!(graph.are_offsets_equal(&explicit, &folded));
        }
    }
    let mut graph = EqualityGraph::default();
    graph.add_int32_equality(&scalar(1), &MachineTerm::constant(2));
    assert!(!graph.are_offsets_equal(&scaled(1, i64::MAX), &PointerOffsetTerm::Constant(-2)));
}

#[test]
fn scaled_int32_restriction_removes_only_unsupported_consequences() {
    let equality = ConditionTerm::equal(scalar(1), scalar(2));
    let explicit = ConditionTerm::pointer_offset_equal(scaled(2, 4), offset(10));
    let context = PureFactContext::new()
        .assume_condition(equality.clone(), true)
        .assume_condition(explicit.clone(), true);
    assert!(
        context
            .equality_graph
            .are_offsets_equal(&scaled(1, 4), &offset(10))
    );
    let restricted = context.restricted_to_facts(&[(equality, true)], &[]);
    assert!(
        restricted
            .equality_graph
            .are_offsets_equal(&scaled(1, 4), &scaled(2, 4))
    );
    assert!(
        !restricted
            .equality_graph
            .are_offsets_equal(&scaled(1, 4), &offset(10))
    );
}

/// The byte offset of `x * 4` at stride one, the spelling `(char *)p + x * 4`
/// keeps when it is formed.
fn byte_product(id: u64, stride: u32, product_first: bool) -> PointerOffsetTerm {
    let (left, right) = if product_first {
        (scalar(id), MachineTerm::constant(stride))
    } else {
        (MachineTerm::constant(stride), scalar(id))
    };
    PointerOffsetTerm::scale_int32(MachineTerm::multiply(left, right), 1)
}

fn no_overflow(id: u64, stride: u32, product_first: bool) -> ConditionTerm {
    if product_first {
        ConditionTerm::signed_multiply_overflows(scalar(id), MachineTerm::constant(stride))
    } else {
        ConditionTerm::signed_multiply_overflows(MachineTerm::constant(stride), scalar(id))
    }
}

/// `!signed_multiply_overflows(x, 4)` joins the byte offset of `x * 4` to
/// element `x` at stride four, whichever is registered first: the fact before
/// either offset node exists, or after both are named by other equalities.
/// Either operand order of the product is read. A fork made before the fact
/// keeps the offsets apart.
#[test]
fn a_byte_product_joins_its_element_offset_in_either_registration_order() {
    for product_first in [true, false] {
        for fact_first in [true, false] {
            let mut graph = EqualityGraph::default();
            if fact_first {
                assert!(graph.add_condition(&no_overflow(1, 4, product_first), false));
            }
            graph.add_offset_equality(&nested(byte_product(1, 4, product_first)), &offset(10));
            graph.add_offset_equality(&nested(scaled(1, 4)), &offset(11));
            let before = graph.clone();
            if !fact_first {
                assert!(!graph.are_offsets_equal(&offset(10), &offset(11)));
                assert!(graph.add_condition(&no_overflow(1, 4, product_first), false));
            }
            assert!(
                graph.are_offsets_equal(&offset(10), &offset(11)),
                "product_first={product_first}, fact_first={fact_first}"
            );
            assert!(graph.are_offsets_equal(&byte_product(1, 4, product_first), &scaled(1, 4)));
            assert_eq!(
                before.are_offsets_equal(&offset(10), &offset(11)),
                fact_first,
                "a fork before the fact must not see it"
            );
        }
    }
}

/// Without the fact the two offsets differ where `x * 4` wraps, so nothing
/// joins them: no fact, an overflow fact that holds, another stride, another
/// index, a stride of one, or two symbolic operands.
#[test]
fn a_byte_product_stays_apart_without_its_no_overflow_fact() {
    let unrelated = |condition: Option<(ConditionTerm, bool)>| {
        let mut graph = EqualityGraph::default();
        if let Some((condition, value)) = condition {
            graph.add_condition(&condition, value);
        }
        graph.are_offsets_equal(&byte_product(1, 4, true), &scaled(1, 4))
    };
    assert!(!unrelated(None));
    assert!(!unrelated(Some((no_overflow(1, 4, true), true))));
    assert!(!unrelated(Some((no_overflow(1, 8, true), false))));
    assert!(!unrelated(Some((no_overflow(2, 4, true), false))));
    let mut graph = EqualityGraph::default();
    graph.add_condition(&no_overflow(1, 8, true), false);
    assert!(!graph.are_offsets_equal(&byte_product(1, 8, true), &scaled(1, 4)));
    assert!(graph.are_offsets_equal(&byte_product(1, 8, true), &scaled(1, 8)));
    assert!(
        crate::kernel::equality_graph::byte_product_offsets(&no_overflow(1, 1, true)).is_none()
    );
    assert!(
        crate::kernel::equality_graph::byte_product_offsets(
            &ConditionTerm::signed_multiply_overflows(scalar(1), scalar(2))
        )
        .is_none()
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/scaled_int32_tests.rs");
}
