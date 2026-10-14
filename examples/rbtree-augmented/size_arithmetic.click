import click::integer;

theorem size_sum_defined(left: int32, right: int32) {
    requires 0 <= left;
    requires 0 <= right;
    requires right <= 2147483646;
    requires left <= 2147483646 - right;
    ensures defined(1 + left + right) by {
        have left <= 2147483646 by {
            arithmetic() using {
                0 <= right;
                right <= 2147483646;
                left <= 2147483646 - right;
            }
        }
        have 1 + left <= 2147483647 - right by {
            arithmetic() using {
                0 <= left;
                left <= 2147483646;
                0 <= right;
                right <= 2147483646;
                left <= 2147483646 - right;
            }
        }
        have defined(1 + left) by auto;
        have defined(2147483647 - right) by auto;
        apply(int32_add_to_integer(1, left));
        apply(int32_subtract_to_integer(2147483647, right));
        apply(int32_less_equal_to_integer(1 + left, 2147483647 - right));
        apply(int32_less_equal_to_integer(0, left));
        apply(int32_less_equal_to_integer(0, right));
        have to_integer(1 + left) + to_integer(right) <= 2147483647 by {
            arithmetic() using {
                to_integer(2147483647 - right) == 2147483647 - to_integer(right);
                to_integer(1 + left) <= to_integer(2147483647 - right);
            }
        }
        have to_integer(1 + left) + to_integer(right) >= -2147483648 by {
            arithmetic() using {
                to_integer(1 + left) == 1 + to_integer(left);
                0 <= to_integer(left);
                0 <= to_integer(right);
            }
        }
        apply(int32_add_defined_by_integer_bounds(1 + left, right));
        assumption();
    }
}

theorem size_sum_as_integer(left: int32, right: int32) {
    requires defined(1 + left + right);
    ensures to_integer(1 + left + right) == 1 + to_integer(left) + to_integer(right) by {
        apply(int32_add_to_integer(1, left));
        apply(int32_add_to_integer(1 + left, right));
        arithmetic() using {
            to_integer(1 + left) == 1 + to_integer(left);
            to_integer(1 + left + right) == to_integer(1 + left) + to_integer(right);
        }
    }
}

// Derive the callback's machine bounds from the mathematical subtree count.
theorem size_children_fit(left: int32, right: int32) {
    requires 0 <= to_integer(left);
    requires 0 <= to_integer(right);
    requires 1 + to_integer(left) + to_integer(right) <= 2147483647;
    ensures 0 <= left by {
        apply(int32_to_integer_less_equal_implies_less_equal(0, left)); assumption();
    }
    ensures 0 <= right by {
        apply(int32_to_integer_less_equal_implies_less_equal(0, right)); assumption();
    }
    ensures right <= 2147483646 by {
        have to_integer(right) <= 2147483646 by {
            arithmetic() using { 0 <= to_integer(left); 1 + to_integer(left) + to_integer(right) <= 2147483647; }
        }
        apply(int32_to_integer_less_equal_implies_less_equal(right, 2147483646)); assumption();
    }
    ensures left <= 2147483646 - right by {
        have to_integer(right) <= 2147483646 by {
            arithmetic() using { 0 <= to_integer(left); 1 + to_integer(left) + to_integer(right) <= 2147483647; }
        }
        apply(int32_to_integer_less_equal_implies_less_equal(0, right));
        apply(int32_to_integer_less_equal_implies_less_equal(right, 2147483646));
        have defined(2147483646 - right) by auto;
        apply(int32_subtract_to_integer(2147483646, right));
        have to_integer(left) <= to_integer(2147483646 - right) by {
            arithmetic() using {
                1 + to_integer(left) + to_integer(right) <= 2147483647;
                to_integer(2147483646 - right) == 2147483646 - to_integer(right);
            }
        }
        apply(int32_to_integer_less_equal_implies_less_equal(left, 2147483646 - right)); assumption();
    }
}
