theorem int32_increment_upper_bound(value: int32, upper: int32) {
    requires value < upper;

    ensures value + 1 <= upper;
}

theorem int32_increment_strictly_increases(value: int32, upper: int32) {
    requires value < upper;

    ensures value < value + 1;
}

theorem int32_increment_lower_bound(value: int32, lower: int32, upper: int32) {
    requires lower <= value;
    requires value < upper;

    ensures lower <= value + 1;
}

theorem int32_increment_greater_equal_lower_bound(value: int32, lower: int32, upper: int32) {
    requires value >= lower;
    requires value < upper;

    ensures value + 1 >= lower;
}

theorem int32_increment_greater_than_lower_bound(value: int32, lower: int32, upper: int32) {
    requires value >= lower;
    requires value < upper;

    ensures value + 1 > lower;
}

theorem int32_increment_preserves_order(value: int32, lower: int32, upper: int32) {
    requires lower <= value;
    requires value < upper;

    ensures lower + 1 <= value + 1;
}

theorem int32_increment_less_equal_implies_less_than(lower: int32, value: int32) {
    requires lower < lower + 1;
    requires lower + 1 <= value;

    ensures lower < value;
}

theorem int32_less_than_increment_implies_less_equal(value: int32, upper: int32) {
    requires value < upper + 1;

    ensures value <= upper;
}

theorem int32_positive_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= value;
}

theorem int32_less_than_implies_less_equal(left: int32, right: int32) {
    requires left < right;

    ensures left <= right;
}

theorem int32_less_than_implies_not_equal(left: int32, right: int32) {
    requires left < right;

    ensures left != right;
}

theorem int32_not_less_than_implies_greater_equal(left: int32, right: int32) {
    requires not (left < right);

    ensures left >= right;
}

theorem int32_increment_below_max_is_defined(value: int32) {
    requires value < 2147483647;

    ensures defined(value + 1);
}

theorem int32_increment_left_below_max_is_defined(value: int32) {
    requires value < 2147483647;

    ensures defined(1 + value);
}

theorem int32_increment_left_strictly_increases(value: int32) {
    requires value < 2147483647;

    ensures value < 1 + value;
}

theorem int32_nonnegative_add_within_max_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires value <= 2147483647 - amount;

    ensures defined(value + amount);
}

theorem int32_nonnegative_subtract_within_value_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires amount <= value;

    ensures defined(value - amount);
}

theorem int32_move_one_from_right_to_left_preserves_sum(
    total: int32,
    left: int32,
    right: int32
) {
    requires 0 <= left;
    requires 1 <= right;
    requires total == left + right;

    ensures total == (left + 1) + (right - 1);
}

theorem int32_subtract_equal_sum_right_cancels(value: int32, left: int32, amount: int32) {
    requires defined(left + amount) and value == left + amount;
    requires defined(value - amount);

    ensures value - amount == left by {
        rewrite(value == left + amount);
        simp();
    }
}

theorem int32_add_nonnegative_right_is_at_least_left(left: int32, right: int32) {
    requires 0 <= right;
    requires defined(left + right);

    ensures left <= left + right;
}

theorem int32_add_nonnegative_left_is_at_least_right(left: int32, right: int32) {
    requires 0 <= left;
    requires defined(left + right);

    ensures right <= left + right;
}

theorem int32_positive_predecessor_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= value - 1;
}

theorem int32_above_one_predecessor_is_at_least_one(value: int32) {
    requires 1 < value;

    ensures value - 1 >= 1;
}

theorem int32_positive_predecessor_strictly_decreases(value: int32) {
    requires 0 < value;

    ensures value - 1 < value;
}

theorem uint32_positive_predecessor_strictly_decreases(value: uint32) {
    requires 0u32 < value;

    ensures value - 1u32 < value;
}

theorem uint32_increment_upper_bound(value: uint32, upper: uint32) {
    requires value < upper;

    ensures value + 1u32 <= upper;
}

theorem uint32_increment_strictly_increases(value: uint32, upper: uint32) {
    requires value < upper;

    ensures value < value + 1u32;
}

theorem uint32_less_than_implies_positive_difference(value: uint32, upper: uint32) {
    requires value < upper;

    ensures 0u32 < upper - value;
}

theorem uint32_difference_decreases_after_increment(value: uint32, bound: uint32) {
    requires value < bound;

    ensures (0u32 - value) + (bound - 1u32) < (0u32 - value) + bound;
}

theorem uint32_less_than_less_equal_transitive(first: uint32, middle: uint32, last: uint32) {
    requires first < middle;
    requires middle <= last;

    ensures first < last;
}

theorem uint32_less_equal_less_than_transitive(first: uint32, middle: uint32, last: uint32) {
    requires first <= middle;
    requires middle < last;

    ensures first < last;
}

theorem uint32_less_than_transitive(first: uint32, middle: uint32, last: uint32) {
    requires first < middle;
    requires middle < last;

    ensures first < last;
}

theorem uint32_less_equal_transitive(first: uint32, middle: uint32, last: uint32) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last;
}

theorem uint64_less_than_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first < middle;
    requires middle <= last;

    ensures first < last;
}

theorem uint64_less_equal_less_than_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first <= middle;
    requires middle < last;

    ensures first < last;
}

theorem uint64_less_than_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first < middle;
    requires middle < last;

    ensures first < last;
}

theorem uint64_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last;
}

theorem uint64_less_equal_and_not_less_than_implies_equal(left: uint64, right: uint64) {
    requires left <= right;
    requires not left < right;

    ensures left == right;
}

theorem int64_less_than_less_equal_transitive(first: int64, middle: int64, last: int64) {
    requires first < middle;
    requires middle <= last;

    ensures first < last;
}

theorem int64_less_equal_less_than_transitive(first: int64, middle: int64, last: int64) {
    requires first <= middle;
    requires middle < last;

    ensures first < last;
}

theorem int64_less_than_transitive(first: int64, middle: int64, last: int64) {
    requires first < middle;
    requires middle < last;

    ensures first < last;
}

theorem int64_less_equal_transitive(first: int64, middle: int64, last: int64) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last;
}

theorem uint32_greater_than_implies_reversed_less_than(greater: uint32, lower: uint32) {
    requires greater > lower;

    ensures lower < greater;
}

theorem uint32_less_than_implies_reversed_greater_than(lower: uint32, greater: uint32) {
    requires lower < greater;

    ensures greater > lower;
}

theorem uint32_greater_equal_implies_reversed_less_equal(greater: uint32, lower: uint32) {
    requires greater >= lower;

    ensures lower <= greater;
}

theorem uint32_less_equal_implies_reversed_greater_equal(lower: uint32, greater: uint32) {
    requires lower <= greater;

    ensures greater >= lower;
}

theorem int32_nonnegative_predecessor_upper_bound(value: int32, bound: int32) {
    requires 0 <= value;
    requires value <= bound;

    ensures value - 1 <= bound;
}

theorem int32_less_equal_less_than_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle < last;

    ensures first < last;
}

theorem int32_less_equal_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last;
}

theorem int32_less_than_transitive(first: int32, middle: int32, last: int32) {
    requires first < middle;
    requires middle < last;

    ensures first < last;
}

theorem int32_less_than_less_equal_transitive(first: int32, middle: int32, last: int32) {
    requires first < middle;
    requires middle <= last;

    ensures first < last;
}

theorem int32_greater_equal_transitive(last: int32, middle: int32, first: int32) {
    requires last >= middle;
    requires middle >= first;

    ensures last >= first;
}

theorem int32_greater_equal_implies_reversed_less_equal(greater: int32, lower: int32) {
    requires greater >= lower;

    ensures lower <= greater;
}

theorem int32_less_equal_implies_reversed_greater_equal(lower: int32, greater: int32) {
    requires lower <= greater;

    ensures greater >= lower;
}

theorem int32_less_equal_and_not_less_than_implies_equal(left: int32, right: int32) {
    requires left <= right;
    requires not (left < right);

    ensures left == right;
}

theorem int32_less_equal_and_not_equal_implies_less_than(left: int32, right: int32) {
    requires left <= right;
    requires left != right;

    ensures left < right;
}

theorem int32_greater_equal_and_not_greater_than_implies_equal(left: int32, right: int32) {
    requires left >= right;
    requires not (left > right);

    ensures left == right;
}
