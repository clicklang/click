import click::integer;

theorem size_sum_defined(left: int32, right: int32) {
    requires 0 <= left;
    requires 0 <= right;
    requires right <= 2147483646;
    requires left <= 2147483646 - right;
    ensures defined(1 + left + right) by {
        have left <= 2147483646 by {
            solve() using {
                0 <= right;
                right <= 2147483646;
                left <= 2147483646 - right;
            };
        }
        have to_integer(1 + left) == to_integer(1) + to_integer(left) by auto();
        have to_integer(2147483647 - right) == to_integer(2147483647) - to_integer(right) by auto();
        have to_integer((1 + left)) <= to_integer((2147483647 - right)) by auto();
        have to_integer(0) <= to_integer(left) by auto();
        have to_integer(0) <= to_integer(right) by auto();
        have to_integer(1 + left) + to_integer(right) <= 2147483647 by {
            solve() using {
                to_integer(2147483647 - right) == 2147483647 - to_integer(right);
                to_integer(1 + left) <= to_integer(2147483647 - right);
            };
        }
        have defined((1 + left) + right) by auto();
        assumption();
    }
}

theorem size_sum_as_integer(left: int32, right: int32) {
    requires defined(1 + left + right);
    ensures to_integer(1 + left + right) == 1 + to_integer(left) + to_integer(right) by {
        have to_integer(1 + left) == to_integer(1) + to_integer(left) by auto();
        have to_integer((1 + left) + right) == to_integer((1 + left)) + to_integer(right) by auto();
        solve() using {
            to_integer(1 + left) == 1 + to_integer(left);
            to_integer(1 + left + right) == to_integer(1 + left) + to_integer(right);
        };
    }
}

// Derive the callback's machine bounds from the mathematical subtree count.
theorem size_children_fit(left: int32, right: int32) {
    requires 0 <= to_integer(left);
    requires 0 <= to_integer(right);
    requires 1 + to_integer(left) + to_integer(right) <= 2147483647;
    ensures 0 <= left by {
        have 0 <= left by auto(); assumption();
    }
    ensures 0 <= right by {
        have 0 <= right by auto(); assumption();
    }
    ensures right <= 2147483646 by {
        have right <= 2147483646 by auto(); assumption();
    }
    ensures left <= 2147483646 - right by {
        have 0 <= right by auto();
        have right <= 2147483646 by auto();
        have to_integer(2147483646 - right) == to_integer(2147483646) - to_integer(right) by auto();
        have left <= (2147483646 - right) by auto(); assumption();
    }
}
