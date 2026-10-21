arithmetic "integer";

// Cache arithmetic when both children of the focused node survive a rotation.
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_double_middle_counts.click";

theorem sized_double_subtrees_bounds(pv: int32, far: SizedTree, middle: SizedTree, other: SizedTree) {
    requires sized_counts_valid(far) == 1;
    requires sized_counts_valid(middle) == 1;
    requires sized_counts_valid(other) == 1;
    requires to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) + to_integer(sized_value(other));
    ensures defined(pv - 1)
        and 0 <= sized_value(far)
        and 0 <= sized_value(middle)
        and 0 <= sized_value(other)
        and sized_value(middle) <= 2147483646
        and sized_value(far) <= 2147483646 - sized_value(middle)
        and sized_value(far) <= 2147483646
        and sized_value(middle) <= 2147483646 - sized_value(far)
        and 1 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) <= 2147483647 by {
        apply(sized_valid_value_nonnegative(far));
        apply(sized_valid_value_nonnegative(middle));
        apply(sized_valid_value_nonnegative(other));
        apply(click::integer::int32_to_integer_bounds(pv));
        have to_integer(pv) - to_integer(1) >= -2147483648 by {
            arithmetic() using {
                to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) + to_integer(sized_value(other));
                0 <= to_integer(sized_value(far));
                0 <= to_integer(sized_value(middle));
                0 <= to_integer(sized_value(other));
            };
        }
        have to_integer(pv) - to_integer(1) <= 2147483647 by {
            arithmetic() using { to_integer(pv) <= 2147483647; };
        }
        apply(click::integer::int32_subtract_defined_by_integer_bounds(pv, 1));
        have 1 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) <= 2147483647 by {
            arithmetic() using {
                to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) + to_integer(sized_value(other));
                to_integer(pv) <= 2147483647;
                0 <= to_integer(sized_value(other));
            };
        }
        have 1 + to_integer(sized_value(middle)) + to_integer(sized_value(far)) <= 2147483647 by {
            arithmetic() using { 1 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) <= 2147483647; };
        }
        apply(size_children_fit(sized_value(far), sized_value(middle)));
        apply(size_children_fit(sized_value(middle), sized_value(far)));
        apply(click::integer::int32_to_integer_less_equal_implies_less_equal(0, sized_value(other)));
        have to_integer(sized_value(far)) <= 2147483646 - to_integer(sized_value(middle)) by {
            arithmetic() using { 1 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) <= 2147483647; };
        }
        have to_integer(sized_value(middle)) <= 2147483646 - to_integer(sized_value(far)) by {
            arithmetic() using { 1 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) <= 2147483647; };
        }
        assumption();
    }
}

theorem sized_double_subtrees_subtract_other_defined(pv: int32, far: SizedTree, middle: SizedTree, other: SizedTree) {
    requires sized_counts_valid(far) == 1;
    requires sized_counts_valid(middle) == 1;
    requires sized_counts_valid(other) == 1;
    requires to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) + to_integer(sized_value(other));
    requires defined(pv - 1);
    ensures defined(pv - 1 - sized_value(other)) by {
        apply(sized_valid_value_nonnegative(far));
        apply(sized_valid_value_nonnegative(middle));
        apply(sized_valid_value_nonnegative(other));
        apply(click::integer::int32_to_integer_bounds(pv));
        apply(click::integer::int32_subtract_to_integer(pv, 1));
        have to_integer(pv - 1) - to_integer(sized_value(other)) >= -2147483648 by {
            arithmetic() using {
                to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) + to_integer(sized_value(other));
                to_integer(pv - 1) == to_integer(pv) - to_integer(1);
                0 <= to_integer(sized_value(far));
                0 <= to_integer(sized_value(middle));
            };
        }
        have to_integer(pv - 1) - to_integer(sized_value(other)) <= 2147483647 by {
            arithmetic() using {
                to_integer(pv - 1) == to_integer(pv) - to_integer(1);
                to_integer(pv) <= 2147483647;
                0 <= to_integer(sized_value(other));
            };
        }
        apply(click::integer::int32_subtract_defined_by_integer_bounds(pv - 1, sized_value(other)));
        apply(click::integer::int32_subtract_to_integer(pv - 1, sized_value(other)));
        assumption();
    }
}

theorem sized_double_subtrees_repaired_count(pv: int32, far: SizedTree, middle: SizedTree, other: SizedTree) {
    requires to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) + to_integer(sized_value(other));
    requires defined(pv - 1);
    requires defined(pv - 1 - sized_value(other));
    ensures to_integer(pv - 1 - sized_value(other)) == 1 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) by {
        apply(click::integer::int32_subtract_to_integer(pv, 1));
        apply(click::integer::int32_subtract_to_integer(pv - 1, sized_value(other)));
        arithmetic() using {
            to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) + to_integer(sized_value(other));
            to_integer(pv - 1) == to_integer(pv) - to_integer(1);
            to_integer(pv - 1 - sized_value(other)) == to_integer(pv - 1) - to_integer(sized_value(other));
        };
    }
}
