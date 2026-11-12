theorem int32_increment_upper_bound(value: int32, upper: int32) {
    requires value < upper;

    ensures to_integer(value + 1) <= to_integer(upper) by {
        arithmetic_certificate signed_int32 {
            premise 0: (value as int32) < (upper as int32) => (value as int32) < (upper as int32);
            int32_range => to_integer(upper as int32) <= to_integer(2147483647 as int32);
            add 0, 1 => (to_integer(value as int32) + to_integer(upper as int32)) < (to_integer(upper as int32) + to_integer(2147483647 as int32));
            interval_from_affine 2 (value) (-2147483648) (2147483646);
            interval_atom (1) (1) (1);
            interval_add_bounded 3, 4 (-2147483647) (2147483647);
            affine_conclusion 0 5 => ((value + 1) as int32) <= (upper as int32);
            conclusion 6;
        }
    }
}

theorem int32_increment_strictly_increases(value: int32, upper: int32) {
    requires value < upper;

    ensures to_integer(value) < to_integer(value + 1) by {
        arithmetic_certificate signed_int32 {
            premise 0: (value as int32) < (upper as int32) => (value as int32) < (upper as int32);
            int32_range => to_integer(upper as int32) <= to_integer(2147483647 as int32);
            add 0, 1 => (to_integer(value as int32) + to_integer(upper as int32)) < (to_integer(upper as int32) + to_integer(2147483647 as int32));
            interval_from_affine 2 (value) (-2147483648) (2147483646);
            interval_atom (1) (1) (1);
            interval_add_bounded 3, 4 (-2147483647) (2147483647);
            trivial => 0 <= 0;
            affine_conclusion 6 5 => (value as int32) < ((value + 1) as int32);
            conclusion 7;
        }
    }
}

theorem int32_increment_lower_bound(value: int32, lower: int32, upper: int32) {
    requires lower <= value;
    requires value < upper;

    ensures to_integer(lower) <= to_integer(value + 1) by {
        arithmetic_certificate signed_int32 {
            premise 0: (lower as int32) <= (value as int32) => (lower as int32) <= (value as int32);
            premise 1: (value as int32) < (upper as int32) => (value as int32) < (upper as int32);
            int32_range => to_integer(-2147483648 as int32) <= to_integer(lower as int32);
            add 0, 2 => (to_integer(lower as int32) + to_integer(-2147483648 as int32)) <= (to_integer(value as int32) + to_integer(lower as int32));
            int32_range => to_integer(upper as int32) <= to_integer(2147483647 as int32);
            add 1, 4 => (to_integer(value as int32) + to_integer(upper as int32)) < (to_integer(upper as int32) + to_integer(2147483647 as int32));
            interval_from_affine 3 (value) (-2147483648) (2147483647);
            interval_from_affine 5 (value) (-2147483648) (2147483646);
            interval_intersect 6, 7 (-2147483648) (2147483646);
            interval_atom (1) (1) (1);
            interval_add_bounded 8, 9 (-2147483647) (2147483647);
            trivial => -1 <= 0;
            add 0, 11 => (to_integer(lower as int32) + -1) <= (to_integer(value as int32) + 0);
            affine_conclusion 12 10 => (lower as int32) <= ((value + 1) as int32);
            conclusion 13;
        }
    }
}

theorem int32_positive_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= value by {
        arithmetic_certificate {
            premise 0: 0 < value => 0 < value;
            trivial => -1 <= 0;
            add 0, 1 => 0 + -1 < (to_integer(value as int32) + 0);
            conclusion 2;
        }
    }
}

theorem int32_increment_below_max_is_defined(value: int32) {
    requires value < 2147483647;

    ensures defined(value + 1) by {
        arithmetic_certificate rules {
            premise 0: value < 2147483647 => value < 2147483647;
            int32_defined bounds [0] => defined(value + 1);
            conclusion 0;
        }
    }
}

theorem int32_nonnegative_add_within_max_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires to_integer(value) <= to_integer(2147483647 - amount);

    ensures defined(value + amount) by {
        have -2147483648 <= 2147483647 - to_integer(amount) by {
            arithmetic_certificate {
                negated_goal => 2147483647 - to_integer(amount) < -2147483648;
                type_range => to_integer(amount) <= 2147483647;
                add 0, 1 => 2147483647 - to_integer(amount) + to_integer(amount) < -2147483648 + 2147483647;
                conclusion 2;
            }
        }
        have 2147483647 - to_integer(amount) <= 2147483647 by {
            arithmetic_certificate {
                negated_goal => 2147483647 < 2147483647 - to_integer(amount);
                premise 0: 0 <= to_integer(amount) => 0 <= to_integer(amount);
                add 0, 1 => 2147483647 + 0 < 2147483647 - to_integer(amount) + to_integer(amount);
                conclusion 2;
            }
        }
        have to_integer(2147483647 - amount) == 2147483647 - to_integer(amount) by {
            arithmetic_certificate rules {
                premise 0: -2147483648 <= 2147483647 - to_integer(amount) => -2147483648 <= 2147483647 - to_integer(amount);
                premise 1: 2147483647 - to_integer(amount) <= 2147483647 => 2147483647 - to_integer(amount) <= 2147483647;
                integer_operation_identity bounds [0, 1] => to_integer(2147483647 - amount) == 2147483647 - to_integer(amount);
                conclusion 0;
            }
        }
        have -2147483648 <= to_integer(value) + to_integer(amount) by {
            arithmetic_certificate {
                negated_goal => to_integer(value) + to_integer(amount) < -2147483648;
                premise 0: 0 <= to_integer(amount) => 0 <= to_integer(amount);
                type_range => -2147483648 <= to_integer(value);
                add 0, 1 => to_integer(value) + to_integer(amount) + 0 < -2147483648 + to_integer(amount);
                add 3, 2 => to_integer(value) + to_integer(amount) + 0 + -2147483648 < -2147483648 + to_integer(amount) + to_integer(value);
                conclusion 4;
            }
        }
        have to_integer(value) + to_integer(amount) <= 2147483647 by {
            arithmetic_certificate {
                negated_goal => 2147483647 < to_integer(value) + to_integer(amount);
                premise 0: to_integer(2147483647 - amount) == 2147483647 - to_integer(amount) => to_integer(2147483647 - amount) == 2147483647 - to_integer(amount);
                less_equal_from_equal 1 => to_integer(2147483647 - amount) <= 2147483647 - to_integer(amount);
                premise 1: to_integer(value) <= to_integer(2147483647 - amount) => to_integer(value) <= to_integer(2147483647 - amount);
                add 0, 2 => 2147483647 + to_integer(2147483647 - amount) < to_integer(value) + to_integer(amount) + (2147483647 - to_integer(amount));
                add 4, 3 => 2147483647 + to_integer(2147483647 - amount) + to_integer(value) < to_integer(value) + to_integer(amount) + (2147483647 - to_integer(amount)) + to_integer(2147483647 - amount);
                conclusion 5;
            }
        }
        assumption();
    }
}

theorem int32_nonnegative_subtract_within_value_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires amount <= value;

    ensures defined(value - amount) by {
        have to_integer(value) <= 2147483647 by {
            arithmetic_certificate {
                type_range => to_integer(value) <= 2147483647;
                conclusion 0;
            }
        }
        have -2147483648 <= to_integer(value) - to_integer(amount) by {
            arithmetic_certificate {
                premise 0: amount <= value => amount <= value;
                trivial => -2147483648 <= 0;
                add 0, 1 => (to_integer(amount as int32) + -2147483648) <= (to_integer(value as int32) + 0);
                conclusion 2;
            }
        }
        have to_integer(value) - to_integer(amount) <= 2147483647 by {
            arithmetic_certificate {
                premise 0: 0 <= amount => 0 <= amount;
                premise 1: to_integer(value) <= 2147483647 => to_integer(value) <= 2147483647;
                add 0, 1 => 0 + to_integer(value) <= (to_integer(amount as int32) + 2147483647);
                conclusion 2;
            }
        }
        assumption();
    }
}

theorem int32_positive_predecessor_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= to_integer(value - 1) by {
        arithmetic_certificate signed_int32 {
            premise 0: (0 as int32) < (value as int32) => (0 as int32) < (value as int32);
            interval_from_affine 0 (value) (1) (2147483647);
            interval_atom (1) (1) (1);
            interval_subtract 1, 2 1 (0) (2147483646);
            affine_conclusion 0 3 => (0 as int32) <= ((value - 1) as int32);
            conclusion 4;
        }
    }
}

theorem int32_positive_predecessor_strictly_decreases(value: int32) {
    requires 0 < value;

    ensures to_integer(value - 1) < to_integer(value) by {
        arithmetic_certificate signed_int32 {
            premise 0: (0 as int32) < (value as int32) => (0 as int32) < (value as int32);
            interval_from_affine 0 (value) (1) (2147483647);
            interval_atom (1) (1) (1);
            interval_subtract 1, 2 1 (0) (2147483646);
            trivial => 0 <= 0;
            affine_conclusion 4 3 => ((value - 1) as int32) < (value as int32);
            conclusion 5;
        }
    }
}

theorem uint32_positive_predecessor_strictly_decreases(value: uint32) {
    requires 0u32 < value;

    ensures to_integer(value - 1u32) < to_integer(value) by {
        have 0 < to_integer(value) by {
            assumption();
        }
        have 0 <= to_integer(value) - 1 by {
            arithmetic_certificate {
                negated_goal => to_integer(value) - 1 < 0;
                premise 0: 0 < to_integer(value) => 0 < to_integer(value);
                add 0, 1 => to_integer(value) - 1 + 1 + (0 + 1) <= 0 + to_integer(value);
                conclusion 2;
            }
        }
        have to_integer(value) - 1 <= 4294967295 by {
            arithmetic_certificate {
                negated_goal => 4294967295 < to_integer(value) - 1;
                type_range => to_integer(value) <= 4294967295;
                add 0, 1 => 4294967295 + to_integer(value) < to_integer(value) - 1 + 4294967295;
                conclusion 2;
            }
        }
        have to_integer(value - 1u32) == to_integer(value) - 1 by {
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(value) - 1 => 0 <= to_integer(value) - 1;
                premise 1: to_integer(value) - 1 <= 4294967295 => to_integer(value) - 1 <= 4294967295;
                integer_operation_identity bounds [0, 1] => to_integer(value - 1u32) == to_integer(value) - 1;
                conclusion 0;
            }
        }
        arithmetic_certificate {
            premise 0: to_integer(value - 1u32) == to_integer(value) - 1 => to_integer(value - 1u32) == to_integer(value) - 1;
            less_equal_from_equal 0 => to_integer(value - 1u32) <= to_integer(value) - 1;
            conclusion 1;
        }
    }
}

theorem uint32_increment_upper_bound(value: uint32, upper: uint32) {
    requires value < upper;

    ensures to_integer(value + 1u32) <= to_integer(upper) by {
        have to_integer(value) < to_integer(upper) by {
            assumption();
        }
        have 0 <= to_integer(value) + 1 by {
            arithmetic_certificate {
                negated_goal => to_integer(value) + 1 < 0;
                type_range => 0 <= to_integer(value);
                add 0, 1 => to_integer(value) + 1 + 0 < 0 + to_integer(value);
                conclusion 2;
            }
        }
        have to_integer(value) + 1 <= 4294967295 by {
            arithmetic_certificate {
                negated_goal => 4294967295 < to_integer(value) + 1;
                premise 0: to_integer(value) < to_integer(upper) => to_integer(value) < to_integer(upper);
                type_range => to_integer(upper) <= 4294967295;
                add 0, 1 => 4294967295 + 1 + (to_integer(value) + 1) <= to_integer(value) + 1 + to_integer(upper);
                add 3, 2 => 4294967295 + 1 + (to_integer(value) + 1) + to_integer(upper) <= to_integer(value) + 1 + to_integer(upper) + 4294967295;
                conclusion 4;
            }
        }
        have to_integer(value + 1u32) == to_integer(value) + 1 by {
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(value) + 1 => 0 <= to_integer(value) + 1;
                premise 1: to_integer(value) + 1 <= 4294967295 => to_integer(value) + 1 <= 4294967295;
                integer_operation_identity bounds [0, 1] => to_integer(value + 1u32) == to_integer(value) + 1;
                conclusion 0;
            }
        }
        arithmetic_certificate {
            premise 0: to_integer(value + 1u32) == to_integer(value) + 1 => to_integer(value + 1u32) == to_integer(value) + 1;
            less_equal_from_equal 0 => to_integer(value + 1u32) <= to_integer(value) + 1;
            premise 1: to_integer(value) < to_integer(upper) => to_integer(value) < to_integer(upper);
            add 1, 2 => to_integer(value + 1u32) + to_integer(value) < to_integer(value) + 1 + to_integer(upper);
            conclusion 3;
        }
    }
}

theorem uint32_less_than_implies_positive_difference(value: uint32, upper: uint32) {
    requires value < upper;

    ensures 0 < to_integer(upper - value) by {
        have 0 <= to_integer(upper) - to_integer(value) by {
            arithmetic_certificate {
                negated_goal => to_integer(upper) - to_integer(value) < 0;
                premise 0: to_integer(value) < to_integer(upper) => to_integer(value) < to_integer(upper);
                add 0, 1 => to_integer(upper) - to_integer(value) + 1 + (to_integer(value) + 1) <= 0 + to_integer(upper);
                conclusion 2;
            }
        }
        have to_integer(upper) - to_integer(value) <= 4294967295 by {
            arithmetic_certificate {
                negated_goal => 4294967295 < to_integer(upper) - to_integer(value);
                type_range => to_integer(upper) <= 4294967295;
                type_range => 0 <= to_integer(value);
                add 0, 1 => 4294967295 + to_integer(upper) < to_integer(upper) - to_integer(value) + 4294967295;
                add 3, 2 => 4294967295 + to_integer(upper) + 0 < to_integer(upper) - to_integer(value) + 4294967295 + to_integer(value);
                conclusion 4;
            }
        }
        have to_integer(upper - value) == to_integer(upper) - to_integer(value) by {
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(upper) - to_integer(value) => 0 <= to_integer(upper) - to_integer(value);
                premise 1: to_integer(upper) - to_integer(value) <= 4294967295 => to_integer(upper) - to_integer(value) <= 4294967295;
                integer_operation_identity bounds [0, 1] => to_integer(upper - value) == to_integer(upper) - to_integer(value);
                conclusion 0;
            }
        }
        arithmetic_certificate {
            negated_goal => to_integer(upper - value) <= 0;
            premise 0: to_integer(upper - value) == to_integer(upper) - to_integer(value) => to_integer(upper - value) == to_integer(upper) - to_integer(value);
            less_equal_from_equal 1 reverse => to_integer(upper) - to_integer(value) <= to_integer(upper - value);
            premise 1: to_integer(value) < to_integer(upper) => to_integer(value) < to_integer(upper);
            add 0, 2 => to_integer(upper - value) + (to_integer(upper) - to_integer(value)) <= 0 + to_integer(upper - value);
            add 4, 3 => to_integer(upper - value) + (to_integer(upper) - to_integer(value)) + to_integer(value) < 0 + to_integer(upper - value) + to_integer(upper);
            conclusion 5;
        }
    }
}

theorem uint32_difference_decreases_after_increment(value: uint32, bound: uint32) {
    requires value < bound;

    ensures to_integer((0u32 - value) + (bound - 1u32)) < to_integer((0u32 - value) + bound) by {
        have (0u32 - value) + (bound - 1u32) == (bound - 1u32) - value by {
            normalize();
        }
        have (0u32 - value) + bound == bound - value by {
            normalize();
        }
        have to_integer((0u32 - value) + (bound - 1u32)) == to_integer((bound - 1u32) - value) by {
            assumption();
        }
        have to_integer((0u32 - value) + bound) == to_integer(bound - value) by {
            assumption();
        }
        have to_integer(value) < to_integer(bound) by {
            normalize() using { value < bound; };
        }
        have 0 <= to_integer(bound) - 1 by {
            arithmetic_certificate {
                negated_goal => to_integer(bound) - 1 < 0;
                premise 0: to_integer(value) < to_integer(bound) => to_integer(value) < to_integer(bound);
                type_range => 0 <= to_integer(value);
                add 0, 1 => to_integer(bound) - 1 + 1 + (to_integer(value) + 1) <= 0 + to_integer(bound);
                add 3, 2 => to_integer(bound) - 1 + 1 + (to_integer(value) + 1) + 0 <= 0 + to_integer(bound) + to_integer(value);
                conclusion 4;
            }
        }
        have to_integer(bound) - 1 <= 4294967295 by {
            arithmetic_certificate {
                negated_goal => 4294967295 < to_integer(bound) - 1;
                type_range => to_integer(bound) <= 4294967295;
                add 0, 1 => 4294967295 + to_integer(bound) < to_integer(bound) - 1 + 4294967295;
                conclusion 2;
            }
        }
        have to_integer(bound - 1u32) == to_integer(bound) - 1 by {
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(bound) - 1 => 0 <= to_integer(bound) - 1;
                premise 1: to_integer(bound) - 1 <= 4294967295 => to_integer(bound) - 1 <= 4294967295;
                integer_operation_identity bounds [0, 1] => to_integer(bound - 1u32) == to_integer(bound) - 1;
                conclusion 0;
            }
        }
        have 0 <= to_integer(bound - 1u32) - to_integer(value) by {
            arithmetic_certificate {
                negated_goal => to_integer(bound - 1u32) - to_integer(value) < 0;
                premise 0: to_integer(bound - 1u32) == to_integer(bound) - 1 => to_integer(bound - 1u32) == to_integer(bound) - 1;
                less_equal_from_equal 1 reverse => to_integer(bound) - 1 <= to_integer(bound - 1u32);
                premise 1: to_integer(value) < to_integer(bound) => to_integer(value) < to_integer(bound);
                add 0, 2 => to_integer(bound - 1u32) - to_integer(value) + (to_integer(bound) - 1) < 0 + to_integer(bound - 1u32);
                add 4, 3 => to_integer(bound - 1u32) - to_integer(value) + (to_integer(bound) - 1) + 1 + (to_integer(value) + 1) <= 0 + to_integer(bound - 1u32) + to_integer(bound);
                conclusion 5;
            }
        }
        have to_integer(bound - 1u32) - to_integer(value) <= 4294967295 by {
            arithmetic_certificate {
                negated_goal => 4294967295 < to_integer(bound - 1u32) - to_integer(value);
                type_range => to_integer(bound - 1u32) <= 4294967295;
                type_range => 0 <= to_integer(value);
                add 0, 1 => 4294967295 + to_integer(bound - 1u32) < to_integer(bound - 1u32) - to_integer(value) + 4294967295;
                add 3, 2 => 4294967295 + to_integer(bound - 1u32) + 0 < to_integer(bound - 1u32) - to_integer(value) + 4294967295 + to_integer(value);
                conclusion 4;
            }
        }
        have to_integer((bound - 1u32) - value) == to_integer(bound - 1u32) - to_integer(value) by {
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(bound - 1u32) - to_integer(value) => 0 <= to_integer(bound - 1u32) - to_integer(value);
                premise 1: to_integer(bound - 1u32) - to_integer(value) <= 4294967295 => to_integer(bound - 1u32) - to_integer(value) <= 4294967295;
                integer_operation_identity bounds [0, 1] => to_integer((bound - 1u32) - value) == to_integer(bound - 1u32) - to_integer(value);
                conclusion 0;
            }
        }
        have 0 <= to_integer(bound) - to_integer(value) by {
            arithmetic_certificate {
                negated_goal => to_integer(bound) - to_integer(value) < 0;
                premise 0: to_integer(value) < to_integer(bound) => to_integer(value) < to_integer(bound);
                add 0, 1 => to_integer(bound) - to_integer(value) + 1 + (to_integer(value) + 1) <= 0 + to_integer(bound);
                conclusion 2;
            }
        }
        have to_integer(bound) - to_integer(value) <= 4294967295 by {
            arithmetic_certificate {
                negated_goal => 4294967295 < to_integer(bound) - to_integer(value);
                type_range => to_integer(bound) <= 4294967295;
                type_range => 0 <= to_integer(value);
                add 0, 1 => 4294967295 + to_integer(bound) < to_integer(bound) - to_integer(value) + 4294967295;
                add 3, 2 => 4294967295 + to_integer(bound) + 0 < to_integer(bound) - to_integer(value) + 4294967295 + to_integer(value);
                conclusion 4;
            }
        }
        have to_integer(bound - value) == to_integer(bound) - to_integer(value) by {
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(bound) - to_integer(value) => 0 <= to_integer(bound) - to_integer(value);
                premise 1: to_integer(bound) - to_integer(value) <= 4294967295 => to_integer(bound) - to_integer(value) <= 4294967295;
                integer_operation_identity bounds [0, 1] => to_integer(bound - value) == to_integer(bound) - to_integer(value);
                conclusion 0;
            }
        }
        arithmetic_certificate {
            negated_goal => to_integer((0u32 - value) + bound) <= to_integer((0u32 - value) + (bound - 1u32));
            premise 0: to_integer((0u32 - value) + (bound - 1u32)) == to_integer((bound - 1u32) - value) => to_integer((0u32 - value) + (bound - 1u32)) == to_integer((bound - 1u32) - value);
            less_equal_from_equal 1 => to_integer((0u32 - value) + (bound - 1u32)) <= to_integer((bound - 1u32) - value);
            premise 1: to_integer((bound - 1u32) - value) == to_integer(bound - 1u32) - to_integer(value) => to_integer((bound - 1u32) - value) == to_integer(bound - 1u32) - to_integer(value);
            less_equal_from_equal 3 => to_integer((bound - 1u32) - value) <= to_integer(bound - 1u32) - to_integer(value);
            premise 2: to_integer(bound - 1u32) == to_integer(bound) - 1 => to_integer(bound - 1u32) == to_integer(bound) - 1;
            less_equal_from_equal 5 => to_integer(bound - 1u32) <= to_integer(bound) - 1;
            premise 3: to_integer((0u32 - value) + bound) == to_integer(bound - value) => to_integer((0u32 - value) + bound) == to_integer(bound - value);
            less_equal_from_equal 7 reverse => to_integer(bound - value) <= to_integer((0u32 - value) + bound);
            premise 4: to_integer(bound - value) == to_integer(bound) - to_integer(value) => to_integer(bound - value) == to_integer(bound) - to_integer(value);
            less_equal_from_equal 9 reverse => to_integer(bound) - to_integer(value) <= to_integer(bound - value);
            add 0, 2 => to_integer((0u32 - value) + bound) + to_integer((0u32 - value) + (bound - 1u32)) <= to_integer((0u32 - value) + (bound - 1u32)) + to_integer((bound - 1u32) - value);
            add 11, 4 => to_integer((0u32 - value) + bound) + to_integer((0u32 - value) + (bound - 1u32)) + to_integer((bound - 1u32) - value) <= to_integer((0u32 - value) + (bound - 1u32)) + to_integer((bound - 1u32) - value) + to_integer(bound - 1u32) - to_integer(value);
            add 12, 6 => to_integer((0u32 - value) + bound) + to_integer((0u32 - value) + (bound - 1u32)) + to_integer((bound - 1u32) - value) + to_integer(bound - 1u32) <= to_integer((0u32 - value) + (bound - 1u32)) + to_integer((bound - 1u32) - value) + to_integer(bound - 1u32) - to_integer(value) + to_integer(bound) - 1;
            add 13, 8 => to_integer((0u32 - value) + bound) + to_integer((0u32 - value) + (bound - 1u32)) + to_integer((bound - 1u32) - value) + to_integer(bound - 1u32) + to_integer(bound - value) <= to_integer((0u32 - value) + (bound - 1u32)) + to_integer((bound - 1u32) - value) + to_integer(bound - 1u32) - to_integer(value) + to_integer(bound) - 1 + to_integer((0u32 - value) + bound);
            add 14, 10 => to_integer((0u32 - value) + bound) + to_integer((0u32 - value) + (bound - 1u32)) + to_integer((bound - 1u32) - value) + to_integer(bound - 1u32) + to_integer(bound - value) + to_integer(bound) - to_integer(value) <= to_integer((0u32 - value) + (bound - 1u32)) + to_integer((bound - 1u32) - value) + to_integer(bound - 1u32) - to_integer(value) + to_integer(bound) - 1 + to_integer((0u32 - value) + bound) + to_integer(bound - value);
            conclusion 15;
        }
    }
}

theorem uint64_less_than_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first < middle;
    requires middle <= last;

    ensures first < last by {
        arithmetic_certificate {
            premise 0: first < middle => first < middle;
            premise 1: middle <= last => middle <= last;
            add 0, 1 => to_integer(first) + to_integer(middle) < to_integer(middle) + to_integer(last);
            conclusion 2;
        }
    }
}

theorem uint64_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last by {
        arithmetic_certificate {
            premise 0: first <= middle => first <= middle;
            premise 1: middle <= last => middle <= last;
            add 0, 1 => to_integer(first) + to_integer(middle) <= to_integer(middle) + to_integer(last);
            conclusion 2;
        }
    }
}

theorem int32_nonnegative_predecessor_upper_bound(value: int32, bound: int32) {
    requires 0 <= value;
    requires value <= bound;

    ensures to_integer(value - 1) <= to_integer(bound) by {
        arithmetic_certificate signed_int32 {
            premise 0: (0 as int32) <= (value as int32) => (0 as int32) <= (value as int32);
            premise 1: (value as int32) <= (bound as int32) => (value as int32) <= (bound as int32);
            interval_from_affine 0 (value) (0) (2147483647);
            interval_atom (1) (1) (1);
            interval_subtract 2, 3 2 (-1) (2147483646);
            trivial => -1 <= 0;
            add 1, 5 => (to_integer(value as int32) + -1) <= (to_integer(bound as int32) + 0);
            affine_conclusion 6 4 => ((value - 1) as int32) <= (bound as int32);
            conclusion 7;
        }
    }
}

theorem int32_less_equal_less_than_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle < last;

    ensures first < last by {
        arithmetic_certificate {
            premise 0: first <= middle => first <= middle;
            premise 1: middle < last => middle < last;
            add 0, 1 => (to_integer(first as int32) + to_integer(middle as int32)) < (to_integer(middle as int32) + to_integer(last as int32));
            conclusion 2;
        }
    }
}

theorem int32_less_equal_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last by {
        arithmetic_certificate {
            premise 0: first <= middle => first <= middle;
            premise 1: middle <= last => middle <= last;
            add 0, 1 => (to_integer(first as int32) + to_integer(middle as int32)) <= (to_integer(middle as int32) + to_integer(last as int32));
            conclusion 2;
        }
    }
}

theorem int32_less_equal_and_not_less_than_implies_equal(left: int32, right: int32) {
    requires left <= right;
    requires not (left < right);

    ensures left == right by {
        arithmetic_certificate {
            premise 0: left <= right => left <= right;
            premise 1: not left < right => not left < right;
            equal_from_bounds 0, 1 => left == right;
            conclusion 2;
        }
    }
}

theorem int32_less_equal_and_not_equal_implies_less_than(left: int32, right: int32) {
    requires left <= right;
    requires left != right;

    ensures left < right by {
        arithmetic_certificate signed_int32 {
            premise 0: (left as int32) <= (right as int32) => (left as int32) <= (right as int32);
            premise 1: (left as int32) != (right as int32) => (left as int32) != (right as int32);
            less_than_from_not_equal 0, 1 => to_integer(left as int32) < to_integer(right as int32);
            conclusion 2;
        }
    }
}

// Wrapping unsigned arithmetic, the C operation itself. A specification that
// means C's modular result writes it with these, so it keeps that meaning
// where `+`, `-` and `*` compare exact Integers.
function uint32_wrapping_add(left: uint32, right: uint32) -> uint32 {
    left + right
}

function uint32_wrapping_sub(left: uint32, right: uint32) -> uint32 {
    left - right
}

function uint32_wrapping_mul(left: uint32, right: uint32) -> uint32 {
    left * right
}

function uint64_wrapping_add(left: uint64, right: uint64) -> uint64 {
    left + right
}

function uint64_wrapping_sub(left: uint64, right: uint64) -> uint64 {
    left - right
}

function uint64_wrapping_mul(left: uint64, right: uint64) -> uint64 {
    left * right
}

theorem uint32_add_to_integer(left: uint32, right: uint32) {
    requires to_integer(left) + to_integer(right) <= 4294967295;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by {
        have 0 <= to_integer(left) + to_integer(right) by {
            arithmetic_certificate {
                negated_goal => to_integer(left) + to_integer(right) < 0;
                type_range => 0 <= to_integer(left);
                type_range => 0 <= to_integer(right);
                add 0, 1 => to_integer(left) + to_integer(right) + 0 < 0 + to_integer(left);
                add 3, 2 => to_integer(left) + to_integer(right) + 0 + 0 < 0 + to_integer(left) + to_integer(right);
                conclusion 4;
            }
        }
        have to_integer(left) + to_integer(right) <= 4294967295 by {
            assumption();
        }
        have to_integer(left + right) == to_integer(left) + to_integer(right) by {
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(left) + to_integer(right) => 0 <= to_integer(left) + to_integer(right);
                premise 1: to_integer(left) + to_integer(right) <= 4294967295 => to_integer(left) + to_integer(right) <= 4294967295;
                integer_operation_identity bounds [0, 1] => to_integer(left + right) == to_integer(left) + to_integer(right);
                conclusion 0;
            }
        }
        assumption();
    }
}

// Exact unsigned subtraction needs the native no-underflow guard.
theorem uint32_subtract_to_integer(left: uint32, right: uint32) {
    requires right <= left;
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have 0 <= to_integer(left) - to_integer(right) by {
            arithmetic_certificate {
                negated_goal => to_integer(left) - to_integer(right) < 0;
                premise 0: to_integer(right) <= to_integer(left) => to_integer(right) <= to_integer(left);
                add 0, 1 => to_integer(left) - to_integer(right) + to_integer(right) < 0 + to_integer(left);
                conclusion 2;
            }
        }
        have to_integer(left) - to_integer(right) <= 4294967295 by {
            arithmetic_certificate {
                negated_goal => 4294967295 < to_integer(left) - to_integer(right);
                type_range => to_integer(left) <= 4294967295;
                type_range => 0 <= to_integer(right);
                add 0, 1 => 4294967295 + to_integer(left) < to_integer(left) - to_integer(right) + 4294967295;
                add 3, 2 => 4294967295 + to_integer(left) + 0 < to_integer(left) - to_integer(right) + 4294967295 + to_integer(right);
                conclusion 4;
            }
        }
        have to_integer(left - right) == to_integer(left) - to_integer(right) by {
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(left) - to_integer(right) => 0 <= to_integer(left) - to_integer(right);
                premise 1: to_integer(left) - to_integer(right) <= 4294967295 => to_integer(left) - to_integer(right) <= 4294967295;
                integer_operation_identity bounds [0, 1] => to_integer(left - right) == to_integer(left) - to_integer(right);
                conclusion 0;
            }
        }
        assumption();
    }
}

theorem uint64_add_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) + to_integer(right) <= 18446744073709551615;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by {
        have 0 <= to_integer(left) + to_integer(right) by {
            arithmetic_certificate {
                negated_goal => to_integer(left) + to_integer(right) < 0;
                type_range => 0 <= to_integer(left);
                type_range => 0 <= to_integer(right);
                add 0, 1 => to_integer(left) + to_integer(right) + 0 < 0 + to_integer(left);
                add 3, 2 => to_integer(left) + to_integer(right) + 0 + 0 < 0 + to_integer(left) + to_integer(right);
                conclusion 4;
            }
        }
        have to_integer(left) + to_integer(right) <= 18446744073709551615 by {
            assumption();
        }
        have to_integer(left + right) == to_integer(left) + to_integer(right) by {
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(left) + to_integer(right) => 0 <= to_integer(left) + to_integer(right);
                premise 1: to_integer(left) + to_integer(right) <= 18446744073709551615 => to_integer(left) + to_integer(right) <= 18446744073709551615;
                integer_operation_identity bounds [0, 1] => to_integer(left + right) == to_integer(left) + to_integer(right);
                conclusion 0;
            }
        }
        assumption();
    }
}

theorem uint64_multiply_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) * to_integer(right) <= 18446744073709551615;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by {
        have 0 <= to_integer(left) by {
            arithmetic_certificate {
                type_range => 0 <= to_integer(left);
                conclusion 0;
            }
        }
        have to_integer(left) <= 18446744073709551615 by {
            arithmetic_certificate {
                type_range => to_integer(left) <= 18446744073709551615;
                conclusion 0;
            }
        }
        have 0 <= to_integer(right) by {
            arithmetic_certificate {
                type_range => 0 <= to_integer(right);
                conclusion 0;
            }
        }
        have to_integer(right) <= 18446744073709551615 by {
            arithmetic_certificate {
                type_range => to_integer(right) <= 18446744073709551615;
                conclusion 0;
            }
        }
        have 0 <= to_integer(left) * to_integer(right) by {
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(left) => 0 <= to_integer(left);
                premise 1: to_integer(left) <= 18446744073709551615 => to_integer(left) <= 18446744073709551615;
                premise 2: 0 <= to_integer(right) => 0 <= to_integer(right);
                premise 3: to_integer(right) <= 18446744073709551615 => to_integer(right) <= 18446744073709551615;
                integer_product_bounds bounds [0, 1, 2, 3] => 0 <= to_integer(left) * to_integer(right);
                conclusion 0;
            }
        }
        arithmetic_certificate rules {
            premise 0: 0 <= to_integer(left) * to_integer(right) => 0 <= to_integer(left) * to_integer(right);
            premise 1: to_integer(left) * to_integer(right) <= 18446744073709551615 => to_integer(left) * to_integer(right) <= 18446744073709551615;
            integer_operation_identity bounds [0, 1] => to_integer(left * right) == to_integer(left) * to_integer(right);
            conclusion 0;
        }
    }
}

theorem uint64_subtract_to_integer(left: uint64, right: uint64) {
    requires to_integer(right) <= to_integer(left);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have 0 <= to_integer(left) - to_integer(right) by {
            arithmetic_certificate {
                negated_goal => to_integer(left) - to_integer(right) < 0;
                premise 0: to_integer(right) <= to_integer(left) => to_integer(right) <= to_integer(left);
                add 0, 1 => to_integer(left) - to_integer(right) + to_integer(right) < 0 + to_integer(left);
                conclusion 2;
            }
        }
        have to_integer(left) - to_integer(right) <= 18446744073709551615 by {
            arithmetic_certificate {
                negated_goal => 18446744073709551615 < to_integer(left) - to_integer(right);
                type_range => to_integer(left) <= 18446744073709551615;
                type_range => 0 <= to_integer(right);
                add 0, 1 => 18446744073709551615 + to_integer(left) < to_integer(left) - to_integer(right) + 18446744073709551615;
                add 3, 2 => 18446744073709551615 + to_integer(left) + 0 < to_integer(left) - to_integer(right) + 18446744073709551615 + to_integer(right);
                conclusion 4;
            }
        }
        have to_integer(left - right) == to_integer(left) - to_integer(right) by {
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(left) - to_integer(right) => 0 <= to_integer(left) - to_integer(right);
                premise 1: to_integer(left) - to_integer(right) <= 18446744073709551615 => to_integer(left) - to_integer(right) <= 18446744073709551615;
                integer_operation_identity bounds [0, 1] => to_integer(left - right) == to_integer(left) - to_integer(right);
                conclusion 0;
            }
        }
        assumption();
    }
}

theorem uint64_divide_to_integer(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right));
}

theorem uint64_remainder_to_integer(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}

theorem uint64_less_equal_to_integer(left: uint64, right: uint64) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by assumption();
}

theorem uint64_to_integer_less_equal_implies_less_equal(left: uint64, right: uint64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by assumption();
}

theorem uint64_less_than_to_integer(left: uint64, right: uint64) {
    requires left < right;
    ensures to_integer(left) < to_integer(right) by assumption();
}

theorem uint64_to_integer_less_than_implies_less_than(left: uint64, right: uint64) {
    requires to_integer(left) < to_integer(right);
    ensures left < right by assumption();
}

theorem uint32_pack_uint16_to_integer(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high);
}

theorem uint32_pack_uint16_high_first_to_integer(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures to_integer((high << 16) | low) == to_integer(low) + 65536 * to_integer(high);
}

// Exact round trips of two bounded fields packed with the high field first.
theorem uint32_unpack_uint16_low(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures (((high << 16) | low) & 65535u32) == low;
}

theorem uint32_unpack_uint16_high(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures ((((high << 16) | low) >> 16) & 65535u32) == high;
}

theorem uint64_pack_uint16_to_integer(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high);
}

// LP64 C saves the same bounded fields in a uint64 result.
theorem uint64_unpack_uint16_low(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures ((low | (high << 16)) & 65535u64) == low;
}

theorem uint64_unpack_uint16_high(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures (((low | (high << 16)) >> 16) & 65535u64) == high;
}

theorem uint64_less_than_implies_not_greater_equal(left: uint64, right: uint64) {
    requires left < right;
    ensures not (left >= right) by assumption();
}

// Exact observations of unsigned division require both evaluation domains.
theorem uint32_divide_to_integer(left: uint32, right: uint32) {
    requires right != 0u32;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right));
}

theorem uint32_remainder_to_integer(left: uint32, right: uint32) {
    requires right != 0u32;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}

theorem uint32_less_equal_to_integer(left: uint32, right: uint32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by assumption();
}

theorem uint32_to_integer_less_equal_implies_less_equal(left: uint32, right: uint32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by assumption();
}

theorem uint32_to_integer_equal_implies_equal(left: uint32, right: uint32) {
    requires to_integer(left) == to_integer(right);
    ensures left == right by assumption();
}

theorem uint32_to_integer_bounds(value: uint32) {
    ensures 0 <= to_integer(value) by {
        have 0u32 <= value;
        apply(integer::uint32_less_equal_to_integer(0u32, value)) using { 0u32 <= value; };
    }
    ensures to_integer(value) <= 4294967295 by {
        have value <= 4294967295u32;
        apply(integer::uint32_less_equal_to_integer(value, 4294967295u32)) using { value <= 4294967295u32; };
    }
}

theorem int32_add_to_integer(left: int32, right: int32) {
    requires defined(left + right);
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by {
        have -2147483648 <= to_integer(left) + to_integer(right) by {
            assumption();
        }
        have to_integer(left) + to_integer(right) <= 2147483647 by {
            assumption();
        }
        have to_integer(left + right) == to_integer(left) + to_integer(right) by {
            arithmetic_certificate rules {
                premise 0: -2147483648 <= to_integer(left) + to_integer(right) => -2147483648 <= to_integer(left) + to_integer(right);
                premise 1: to_integer(left) + to_integer(right) <= 2147483647 => to_integer(left) + to_integer(right) <= 2147483647;
                integer_operation_identity bounds [0, 1] => to_integer(left + right) == to_integer(left) + to_integer(right);
                conclusion 0;
            }
        }
        assumption();
    }
}

theorem int32_less_equal_to_integer(left: int32, right: int32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by assumption();
}

theorem int32_to_integer_less_equal_implies_less_equal(left: int32, right: int32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by assumption();
}

theorem int64_less_equal_to_integer(left: int64, right: int64) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by assumption();
}

theorem int64_less_than_to_integer(left: int64, right: int64) {
    requires left < right;
    ensures to_integer(left) < to_integer(right) by assumption();
}

theorem int64_greater_equal_to_integer(left: int64, right: int64) {
    requires left >= right;
    ensures to_integer(left) >= to_integer(right) by assumption();
}

theorem int64_to_integer_less_equal_implies_less_equal(left: int64, right: int64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by assumption();
}

theorem int64_to_integer_equal_implies_equal(left: int64, right: int64) {
    requires to_integer(left) == to_integer(right);
    ensures left == right by assumption();
}

theorem int32_subtract_to_integer(left: int32, right: int32) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have -2147483648 <= to_integer(left) - to_integer(right) by {
            assumption();
        }
        have to_integer(left) - to_integer(right) <= 2147483647 by {
            assumption();
        }
        have to_integer(left - right) == to_integer(left) - to_integer(right) by {
            arithmetic_certificate rules {
                premise 0: -2147483648 <= to_integer(left) - to_integer(right) => -2147483648 <= to_integer(left) - to_integer(right);
                premise 1: to_integer(left) - to_integer(right) <= 2147483647 => to_integer(left) - to_integer(right) <= 2147483647;
                integer_operation_identity bounds [0, 1] => to_integer(left - right) == to_integer(left) - to_integer(right);
                conclusion 0;
            }
        }
        assumption();
    }
}

theorem int32_remainder_to_integer(left: int32, right: int32) {
    requires defined(left % right);
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}

theorem int32_add_defined_by_integer_bounds(left: int32, right: int32) {
    requires to_integer(left) + to_integer(right) >= -2147483648;
    requires to_integer(left) + to_integer(right) <= 2147483647;
    ensures defined(left + right) by {
        assumption();
    }
}

theorem to_int8_round_trip(z: Integer) {
    requires z >= -128;
    requires z <= 127;
    ensures to_integer(to_int8(z)) == z;
}

theorem to_int16_round_trip(z: Integer) {
    requires z >= -32768;
    requires z <= 32767;
    ensures to_integer(to_int16(z)) == z;
}

theorem to_int32_round_trip(z: Integer) {
    requires z >= -2147483648;
    requires z <= 2147483647;
    ensures to_integer(to_int32(z)) == z;
}

theorem to_uint8_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 255;
    ensures to_integer(to_uint8(z)) == z;
}

theorem to_uint16_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 65535;
    ensures to_integer(to_uint16(z)) == z;
}

theorem to_uint32_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 4294967295;
    ensures to_integer(to_uint32(z)) == z;
}

theorem to_int64_round_trip(z: Integer) {
    requires z >= -9223372036854775808;
    requires z <= 9223372036854775807;
    ensures to_integer(to_int64(z)) == z;
}

theorem to_uint64_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 18446744073709551615;
    ensures to_integer(to_uint64(z)) == z;
}

theorem int64_subtract_to_integer(left: int64, right: int64) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have -9223372036854775808 <= to_integer(left) - to_integer(right) by {
            assumption();
        }
        have to_integer(left) - to_integer(right) <= 9223372036854775807 by {
            assumption();
        }
        have to_integer(left - right) == to_integer(left) - to_integer(right) by {
            arithmetic_certificate rules {
                premise 0: -9223372036854775808 <= to_integer(left) - to_integer(right) => -9223372036854775808 <= to_integer(left) - to_integer(right);
                premise 1: to_integer(left) - to_integer(right) <= 9223372036854775807 => to_integer(left) - to_integer(right) <= 9223372036854775807;
                integer_operation_identity bounds [0, 1] => to_integer(left - right) == to_integer(left) - to_integer(right);
                conclusion 0;
            }
        }
        assumption();
    }
}

theorem truncation_identity(n: Integer, d: Integer) {
    requires d != 0;
    ensures n == truncating_quotient(n, d) * d + truncating_remainder(n, d);
}

theorem positive_divisor_remainder_lower(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures 1 - d <= truncating_remainder(n, d);
}

theorem positive_divisor_remainder_upper(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures truncating_remainder(n, d) <= d - 1;
}

theorem nonnegative_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 <= n;
    ensures 0 <= truncating_remainder(n, d);
}

theorem nonpositive_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires n <= 0;
    ensures truncating_remainder(n, d) <= 0;
}


theorem multiply_add(a: Integer, b: Integer, c: Integer) {
    ensures (a + b) * c == a * c + b * c by {
        arithmetic_certificate rules {
            integer_polynomial_identity bounds [] => (a + b) * c == a * c + b * c;
            conclusion 0;
        }
    }
}

theorem floor_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires r < 0 implies value == q + -1;
    requires 0 <= r implies value == q;
    ensures value * d <= n by {
        if r < 0 {
            have value == q + -1;
            apply(integer::multiply_add(q, -1, d));
            rewrite(value == q + -1);
            rewrite((q + -1) * d == q * d + -1 * d);
            solve() using { n == q * d + r; 1 - d <= r; };
        } else {
            have 0 <= r by { solve() using { not (r < 0); }; }
            have value == q;
            rewrite(value == q);
            solve() using { n == q * d + r; 0 <= r; };
        }
    }
    ensures n < (value + 1) * d by {
        if r < 0 {
            have value == q + -1;
            have value + 1 == q by { solve() using { value == q + -1; }; }
            rewrite(value + 1 == q);
            solve() using { n == q * d + r; r < 0; };
        } else {
            have 0 <= r by { solve() using { not (r < 0); }; }
            have value == q;
            apply(integer::multiply_add(q, 1, d));
            rewrite(value == q);
            rewrite((q + 1) * d == q * d + 1 * d);
            solve() using { n == q * d + r; r <= d - 1; };
        }
    }
}

theorem ceiling_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires 0 < r implies value == q + 1;
    requires r <= 0 implies value == q;
    ensures n <= value * d by {
        if 0 < r {
            have value == q + 1;
            apply(integer::multiply_add(q, 1, d));
            rewrite(value == q + 1);
            rewrite((q + 1) * d == q * d + 1 * d);
            solve() using { n == q * d + r; r <= d - 1; };
        } else {
            have r <= 0 by { solve() using { not (0 < r); }; }
            have value == q;
            rewrite(value == q);
            solve() using { n == q * d + r; r <= 0; };
        }
    }
    ensures (value + -1) * d < n by {
        if 0 < r {
            have value == q + 1;
            have value + -1 == q by { solve() using { value == q + 1; }; }
            rewrite(value + -1 == q);
            solve() using { n == q * d + r; 0 < r; };
        } else {
            have r <= 0 by { solve() using { not (0 < r); }; }
            have value == q;
            apply(integer::multiply_add(q, -1, d));
            rewrite(value == q);
            rewrite((q + -1) * d == q * d + -1 * d);
            solve() using { n == q * d + r; 1 - d <= r; };
        }
    }
}

theorem positive_divisor_quotient_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound * d <= n;
    ensures bound <= truncating_quotient(n, d) by {
        arithmetic_certificate rules {
            premise 0: bound * d <= n => bound * d <= n;
            premise 1: 1 <= d => 1 <= d;
            integer_quotient_bound bounds [0, 1] => bound <= truncating_quotient(n, d);
            conclusion 0;
        }
    }
}

theorem positive_divisor_quotient_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires n <= bound * d;
    ensures truncating_quotient(n, d) <= bound by {
        arithmetic_certificate rules {
            premise 0: n <= bound * d => n <= bound * d;
            premise 1: 1 <= d => 1 <= d;
            integer_quotient_bound bounds [0, 1] => truncating_quotient(n, d) <= bound;
            conclusion 0;
        }
    }
}

theorem positive_divisor_quotient_strict_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound < 0;
    requires bound * d < n;
    ensures bound < truncating_quotient(n, d) by {
        have bound * d <= n by { solve() using { bound * d < n; }; }
        apply(integer::positive_divisor_quotient_lower(n, d, bound));
        if bound < truncating_quotient(n, d) {
            assumption();
        } else {
            have truncating_quotient(n, d) == bound by { solve() using {
                bound <= truncating_quotient(n, d); not (bound < truncating_quotient(n, d));
            }; }
            if n <= 0 {
                have 0 < d by { solve() using { 1 <= d; }; }
                apply(integer::nonpositive_dividend_remainder(n, d));
                apply(integer::truncation_identity(n, d));
                have n == bound * d + truncating_remainder(n, d) by {
                    rewrite(bound == truncating_quotient(n, d));
                    assumption();
                }
                have not (bound * d < n) by { solve() using {
                    n == bound * d + truncating_remainder(n, d); truncating_remainder(n, d) <= 0;
                }; }
                contradiction(bound * d < n);
            } else {
                have 0 <= n by { solve() using { not (n <= 0); }; }
                have 0 * d <= n by { solve() using { 0 <= n; }; }
                apply(integer::positive_divisor_quotient_lower(n, d, 0));
                have not (bound < 0) by { solve() using {
                    0 <= truncating_quotient(n, d); truncating_quotient(n, d) == bound;
                }; }
                contradiction(bound < 0);
            }
        }
    }
}

theorem positive_divisor_quotient_strict_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 < bound;
    requires n < bound * d;
    ensures truncating_quotient(n, d) < bound by {
        have n <= bound * d by { solve() using { n < bound * d; }; }
        apply(integer::positive_divisor_quotient_upper(n, d, bound));
        if truncating_quotient(n, d) < bound {
            assumption();
        } else {
            have truncating_quotient(n, d) == bound by { solve() using {
                truncating_quotient(n, d) <= bound; not (truncating_quotient(n, d) < bound);
            }; }
            if 0 <= n {
                have 0 < d by { solve() using { 1 <= d; }; }
                apply(integer::nonnegative_dividend_remainder(n, d));
                apply(integer::truncation_identity(n, d));
                have n == bound * d + truncating_remainder(n, d) by {
                    rewrite(bound == truncating_quotient(n, d));
                    assumption();
                }
                have not (n < bound * d) by { solve() using {
                    n == bound * d + truncating_remainder(n, d); 0 <= truncating_remainder(n, d);
                }; }
                contradiction(n < bound * d);
            } else {
                have n <= 0 by { solve() using { not (0 <= n); }; }
                have n <= 0 * d by { solve() using { n <= 0; }; }
                apply(integer::positive_divisor_quotient_upper(n, d, 0));
                have not (0 < bound) by { solve() using {
                    truncating_quotient(n, d) <= 0; truncating_quotient(n, d) == bound;
                }; }
                contradiction(0 < bound);
            }
        }
    }
}

theorem lower_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, lower: Integer) {
    requires lower <= q;
    requires lower * d <= n;
    requires n == q * d + r;
    requires r < 0;
    ensures lower + 1 <= q by {
        if lower + 1 <= q {
            assumption();
        } else {
            have q == lower by { solve() using { lower <= q; not (lower + 1 <= q); }; }
            have n == lower * d + r by {
                rewrite(lower == q);
                assumption();
            }
            have not (r < 0) by { solve() using { lower * d <= n; n == lower * d + r; }; }
            contradiction(r < 0);
        }
    }
}

theorem upper_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, upper: Integer) {
    requires q <= upper;
    requires n <= upper * d;
    requires n == q * d + r;
    requires 0 < r;
    ensures q <= upper + -1 by {
        if q <= upper + -1 {
            assumption();
        } else {
            have q == upper by { solve() using { q <= upper; not (q <= upper + -1); }; }
            have n == upper * d + r by {
                rewrite(upper == q);
                assumption();
            }
            have not (0 < r) by { solve() using { n <= upper * d; n == upper * d + r; }; }
            contradiction(0 < r);
        }
    }
}
theorem multiply_order_nonnegative(a: Integer, b: Integer, factor: Integer) {
    requires a <= b;
    requires 0 <= factor;
    ensures a * factor <= b * factor by {
        arithmetic_certificate rules {
            premise 0: a <= b => a <= b;
            premise 1: 0 <= factor => 0 <= factor;
            integer_multiply_order bounds [0, 1] => a * factor <= b * factor;
            conclusion 0;
        }
    }
}

theorem multiply_order_nonpositive(a: Integer, b: Integer, factor: Integer) {
    requires a <= b;
    requires factor <= 0;
    ensures b * factor <= a * factor by {
        arithmetic_certificate rules {
            premise 0: a <= b => a <= b;
            premise 1: factor <= 0 => factor <= 0;
            integer_multiply_order bounds [0, 1] => b * factor <= a * factor;
            conclusion 0;
        }
    }
}

theorem scaled_product_bounds(value: Integer, amount: Integer, size: Integer, lower: Integer, upper: Integer) {
    requires lower <= value;
    requires value <= upper;
    requires lower <= 0;
    requires 0 <= upper;
    requires 0 <= amount;
    requires amount <= size;
    ensures lower * size <= value * amount by {
        apply(integer::multiply_order_nonnegative(lower, value, amount));
        have lower * size <= lower * amount by {
            arithmetic_certificate rules {
                premise 0: amount <= size => amount <= size;
                premise 1: lower <= 0 => lower <= 0;
                integer_multiply_order bounds [0, 1] => lower * size <= lower * amount;
                conclusion 0;
            }
        }
        solve() using { lower * size <= lower * amount; lower * amount <= value * amount; };
    }
    ensures value * amount <= upper * size by {
        apply(integer::multiply_order_nonnegative(value, upper, amount));
        have upper * amount <= upper * size by {
            arithmetic_certificate rules {
                premise 0: amount <= size => amount <= size;
                premise 1: 0 <= upper => 0 <= upper;
                integer_multiply_order bounds [0, 1] => upper * amount <= upper * size;
                conclusion 0;
            }
        }
        solve() using { value * amount <= upper * amount; upper * amount <= upper * size; };
    }
}

// Unsigned 32-bit product and remainder laws, proved from the division
// observations and the truncating-division lemmas above.
theorem uint32_multiply_to_integer(left: uint32, right: uint32) {
    requires right == 0u32 or left <= 4294967295u32 / right;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by {
        have 0 <= to_integer(left) by {
            normalize();
        }
        have to_integer(left) <= 4294967295 by {
            normalize();
        }
        have 0 <= to_integer(right) by {
            normalize();
        }
        have to_integer(right) <= 4294967295 by {
            normalize();
        }
        have 0 <= to_integer(left) * to_integer(right) by {
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(left) => 0 <= to_integer(left);
                premise 1: to_integer(left) <= 4294967295 => to_integer(left) <= 4294967295;
                premise 2: 0 <= to_integer(right) => 0 <= to_integer(right);
                premise 3: to_integer(right) <= 4294967295 => to_integer(right) <= 4294967295;
                integer_product_bounds bounds [0, 1, 2, 3] => 0 <= to_integer(left) * to_integer(right);
                conclusion 0;
            }
        }
        if right == 0u32 {
            have to_integer(right) <= 0 by {
                normalize() using { right == 0u32; };
            }
            have to_integer(left) * to_integer(right) <= 0 by {
                arithmetic_certificate rules {
                    premise 0: 0 <= to_integer(left) => 0 <= to_integer(left);
                    premise 1: to_integer(left) <= 4294967295 => to_integer(left) <= 4294967295;
                    premise 2: 0 <= to_integer(right) => 0 <= to_integer(right);
                    premise 3: to_integer(right) <= 0 => to_integer(right) <= 0;
                    integer_product_bounds bounds [0, 1, 2, 3] => to_integer(left) * to_integer(right) <= 0;
                    conclusion 0;
                }
            }
            have to_integer(left) * to_integer(right) <= 4294967295 by {
                arithmetic_certificate {
                    premise 0: to_integer(left) * to_integer(right) <= 0 => to_integer(left) * to_integer(right) <= 0;
                    trivial => -4294967295 <= 0;
                    add 0, 1 => to_integer(left) * to_integer(right) + -4294967295 <= 0 + 0;
                    conclusion 2;
                }
            }
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(left) * to_integer(right) => 0 <= to_integer(left) * to_integer(right);
                premise 1: to_integer(left) * to_integer(right) <= 4294967295 => to_integer(left) * to_integer(right) <= 4294967295;
                integer_operation_identity bounds [0, 1] => to_integer(left * right) == to_integer(left) * to_integer(right);
                conclusion 0;
            }
        } else {
            have left <= 4294967295u32 / right by {
                cases {
                    right == 0u32 => {
                        contradiction(right == 0u32);
                    }
                    left <= 4294967295u32 / right => {
                        assumption();
                    }
                }
            }
            have right != 0u32 by {
                normalize() using { not right == 0u32; };
            }
            have 1 <= to_integer(right) by {
                arithmetic_certificate {
                    excluded_bound 0: to_integer(right) != 0 => 1 <= to_integer(right);
                    conclusion 0;
                }
            }
            apply(integer::uint32_divide_to_integer(4294967295u32, right)) using {
                right != 0u32;
                to_integer(right) != 0;
            };
            apply(integer::truncation_identity(4294967295, to_integer(right))) using {
                to_integer(right) != 0;
            };
            apply(integer::nonnegative_dividend_remainder(4294967295, to_integer(right))) using {
                to_integer(right) != 0;
            };
            have 0 <= truncating_quotient(4294967295, to_integer(right)) - to_integer(left) by {
                arithmetic_certificate {
                    negated_goal => truncating_quotient(4294967295, to_integer(right)) - to_integer(left) < 0;
                    premise 0: to_integer(left) <= to_integer(4294967295u32 / right) => to_integer(left) <= to_integer(4294967295u32 / right);
                    premise 1: to_integer(4294967295u32 / right) == truncating_quotient(4294967295, to_integer(right)) => to_integer(4294967295u32 / right) == truncating_quotient(4294967295, to_integer(right));
                    less_equal_from_equal 2 => to_integer(4294967295u32 / right) <= truncating_quotient(4294967295, to_integer(right));
                    add 0, 1 => truncating_quotient(4294967295, to_integer(right)) - to_integer(left) + to_integer(left) < 0 + to_integer(4294967295u32 / right);
                    add 4, 3 => truncating_quotient(4294967295, to_integer(right)) - to_integer(left) + to_integer(left) + to_integer(4294967295u32 / right) < 0 + to_integer(4294967295u32 / right) + truncating_quotient(4294967295, to_integer(right));
                    conclusion 5;
                }
            }
            have truncating_quotient(4294967295, to_integer(right)) - to_integer(left) <= 4294967295 by {
                arithmetic_certificate {
                    negated_goal => 4294967295 < truncating_quotient(4294967295, to_integer(right)) - to_integer(left);
                    premise 0: to_integer(4294967295u32 / right) == truncating_quotient(4294967295, to_integer(right)) => to_integer(4294967295u32 / right) == truncating_quotient(4294967295, to_integer(right));
                    less_equal_from_equal 1 reverse => truncating_quotient(4294967295, to_integer(right)) <= to_integer(4294967295u32 / right);
                    type_range => to_integer(4294967295u32 / right) <= 4294967295;
                    type_range => 0 <= to_integer(left);
                    add 0, 2 => 4294967295 + truncating_quotient(4294967295, to_integer(right)) < truncating_quotient(4294967295, to_integer(right)) - to_integer(left) + to_integer(4294967295u32 / right);
                    add 5, 3 => 4294967295 + truncating_quotient(4294967295, to_integer(right)) + to_integer(4294967295u32 / right) < truncating_quotient(4294967295, to_integer(right)) - to_integer(left) + to_integer(4294967295u32 / right) + 4294967295;
                    add 6, 4 => 4294967295 + truncating_quotient(4294967295, to_integer(right)) + to_integer(4294967295u32 / right) + 0 < truncating_quotient(4294967295, to_integer(right)) - to_integer(left) + to_integer(4294967295u32 / right) + 4294967295 + to_integer(left);
                    conclusion 7;
                }
            }
            have 0 <= (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right) by {
                arithmetic_certificate rules {
                    premise 0: 0 <= truncating_quotient(4294967295, to_integer(right)) - to_integer(left) => 0 <= truncating_quotient(4294967295, to_integer(right)) - to_integer(left);
                    premise 1: truncating_quotient(4294967295, to_integer(right)) - to_integer(left) <= 4294967295 => truncating_quotient(4294967295, to_integer(right)) - to_integer(left) <= 4294967295;
                    premise 2: 0 <= to_integer(right) => 0 <= to_integer(right);
                    premise 3: to_integer(right) <= 4294967295 => to_integer(right) <= 4294967295;
                    integer_product_bounds bounds [0, 1, 2, 3] => 0 <= (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right);
                    conclusion 0;
                }
            }
            have (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right) == truncating_quotient(4294967295, to_integer(right)) * to_integer(right) - to_integer(left) * to_integer(right) by {
                arithmetic_certificate rules {
                    integer_polynomial_identity bounds [] => (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right) == truncating_quotient(4294967295, to_integer(right)) * to_integer(right) - to_integer(left) * to_integer(right);
                    conclusion 0;
                }
            }
            have to_integer(left) * to_integer(right) <= 4294967295 by {
                arithmetic_certificate {
                    negated_goal => 4294967295 < to_integer(left) * to_integer(right);
                    premise 0: 0 <= truncating_remainder(4294967295, to_integer(right)) => 0 <= truncating_remainder(4294967295, to_integer(right));
                    premise 1: 0 <= (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right) => 0 <= (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right);
                    premise 2: 4294967295 == truncating_quotient(4294967295, to_integer(right)) * to_integer(right) + truncating_remainder(4294967295, to_integer(right)) => 4294967295 == truncating_quotient(4294967295, to_integer(right)) * to_integer(right) + truncating_remainder(4294967295, to_integer(right));
                    less_equal_from_equal 3 reverse => truncating_quotient(4294967295, to_integer(right)) * to_integer(right) + truncating_remainder(4294967295, to_integer(right)) <= 4294967295;
                    premise 3: (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right) == truncating_quotient(4294967295, to_integer(right)) * to_integer(right) - to_integer(left) * to_integer(right) => (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right) == truncating_quotient(4294967295, to_integer(right)) * to_integer(right) - to_integer(left) * to_integer(right);
                    less_equal_from_equal 5 => (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right) <= truncating_quotient(4294967295, to_integer(right)) * to_integer(right) - to_integer(left) * to_integer(right);
                    add 0, 1 => 4294967295 + 0 < to_integer(left) * to_integer(right) + truncating_remainder(4294967295, to_integer(right));
                    add 7, 2 => 4294967295 + 0 + 0 < to_integer(left) * to_integer(right) + truncating_remainder(4294967295, to_integer(right)) + (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right);
                    add 8, 4 => 4294967295 + 0 + 0 + truncating_quotient(4294967295, to_integer(right)) * to_integer(right) + truncating_remainder(4294967295, to_integer(right)) < to_integer(left) * to_integer(right) + truncating_remainder(4294967295, to_integer(right)) + (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right) + 4294967295;
                    add 9, 6 => 4294967295 + 0 + 0 + truncating_quotient(4294967295, to_integer(right)) * to_integer(right) + truncating_remainder(4294967295, to_integer(right)) + (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right) < to_integer(left) * to_integer(right) + truncating_remainder(4294967295, to_integer(right)) + (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right) + 4294967295 + truncating_quotient(4294967295, to_integer(right)) * to_integer(right) - to_integer(left) * to_integer(right);
                    conclusion 10;
                }
            }
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(left) * to_integer(right) => 0 <= to_integer(left) * to_integer(right);
                premise 1: to_integer(left) * to_integer(right) <= 4294967295 => to_integer(left) * to_integer(right) <= 4294967295;
                integer_operation_identity bounds [0, 1] => to_integer(left * right) == to_integer(left) * to_integer(right);
                conclusion 0;
            }
        }
    }
}

theorem uint32_multiply_guard_by_integer_bound(left: uint32, right: uint32) {
    requires to_integer(left) * to_integer(right) <= 4294967295;
    ensures right == 0u32 or left <= 4294967295u32 / right by {
        if right == 0u32 {
            assumption();
        } else {
            have right != 0u32 by {
                normalize() using { not right == 0u32; };
            }
            have 1 <= to_integer(right) by {
                arithmetic_certificate {
                    excluded_bound 0: to_integer(right) != 0 => 1 <= to_integer(right);
                    conclusion 0;
                }
            }
            apply(integer::positive_divisor_quotient_lower(4294967295, to_integer(right), to_integer(left))) using {
                to_integer(right) != 0;
                1 <= to_integer(right);
                to_integer(left) * to_integer(right) <= 4294967295;
            };
            apply(integer::uint32_divide_to_integer(4294967295u32, right)) using {
                right != 0u32;
                to_integer(right) != 0;
            };
            have to_integer(left) <= to_integer(4294967295u32 / right) by {
                assumption();
            }
            have left <= 4294967295u32 / right by {
                normalize() using { to_integer(left) <= to_integer(4294967295u32 / right); };
            }
            assumption();
        }
    }
}

theorem uint32_remainder_less_than_divisor(value: uint32, divisor: uint32) {
    requires divisor != 0u32;
    ensures value % divisor < divisor by {
        have 1 <= to_integer(divisor) by {
            arithmetic_certificate {
                excluded_bound 0: to_integer(divisor) != 0 => 1 <= to_integer(divisor);
                conclusion 0;
            }
        }
        have to_integer(divisor) != 0 by {
            arithmetic_certificate rules {
                premise 0: 1 <= to_integer(divisor) => 1 <= to_integer(divisor);
                integer_bound_exclusion bounds [0] => to_integer(divisor) != 0;
                conclusion 0;
            }
        }
        have 0 < to_integer(divisor) by {
            arithmetic_certificate {
                premise 0: 1 <= to_integer(divisor) => 1 <= to_integer(divisor);
                conclusion 0;
            }
        }
        apply(integer::uint32_remainder_to_integer(value, divisor)) using {
            divisor != 0u32;
            to_integer(divisor) != 0;
        };
        apply(integer::positive_divisor_remainder_upper(to_integer(value), to_integer(divisor))) using {
            to_integer(divisor) != 0;
            0 < to_integer(divisor);
        };
        arithmetic_certificate {
            negated_goal => to_integer(divisor) <= to_integer(value % divisor);
            premise 0: to_integer(value % divisor) == truncating_remainder(to_integer(value), to_integer(divisor)) => to_integer(value % divisor) == truncating_remainder(to_integer(value), to_integer(divisor));
            premise 1: truncating_remainder(to_integer(value), to_integer(divisor)) <= to_integer(divisor) - 1 => truncating_remainder(to_integer(value), to_integer(divisor)) <= to_integer(divisor) - 1;
            less_equal_from_equal 1 => to_integer(value % divisor) <= truncating_remainder(to_integer(value), to_integer(divisor));
            add 0, 3 => to_integer(divisor) + to_integer(value % divisor) <= to_integer(value % divisor) + truncating_remainder(to_integer(value), to_integer(divisor));
            add 4, 2 => to_integer(divisor) + to_integer(value % divisor) + truncating_remainder(to_integer(value), to_integer(divisor)) <= to_integer(value % divisor) + truncating_remainder(to_integer(value), to_integer(divisor)) + to_integer(divisor) - 1;
            conclusion 5;
        }
    }
}

theorem uint32_less_than_divisor_implies_remainder_is_value(value: uint32, divisor: uint32) {
    requires value < divisor;
    ensures value % divisor == value by {
        have to_integer(value) < to_integer(divisor) by {
            normalize() using { value < divisor; };
        }
        have 0 <= to_integer(value) by {
            normalize();
        }
        have 1 <= to_integer(divisor) by {
            arithmetic_certificate {
                premise 0: to_integer(value) < to_integer(divisor) => to_integer(value) < to_integer(divisor);
                type_range => 0 <= to_integer(value);
                add 0, 1 => to_integer(value) + 0 < to_integer(divisor) + to_integer(value);
                conclusion 2;
            }
        }
        have to_integer(divisor) != 0 by {
            normalize() using { 1 <= to_integer(divisor); };
        }
        have divisor != 0u32 by {
            normalize() using { to_integer(divisor) != 0; };
        }
        apply(integer::uint32_remainder_to_integer(value, divisor)) using {
            divisor != 0u32;
            to_integer(divisor) != 0;
        };
        have 0 * to_integer(divisor) <= to_integer(value) by {
            arithmetic_certificate {
                premise 0: 0 <= to_integer(value) => 0 <= to_integer(value);
                conclusion 0;
            }
        }
        apply(integer::positive_divisor_quotient_lower(to_integer(value), to_integer(divisor), 0)) using {
            to_integer(divisor) != 0;
            1 <= to_integer(divisor);
            0 * to_integer(divisor) <= to_integer(value);
        };
        have to_integer(value) < 1 * to_integer(divisor) by {
            arithmetic_certificate {
                premise 0: to_integer(value) < to_integer(divisor) => to_integer(value) < to_integer(divisor);
                conclusion 0;
            }
        }
        have 0 < 1 by {
            normalize();
        }
        apply(integer::positive_divisor_quotient_strict_upper(to_integer(value), to_integer(divisor), 1)) using {
            to_integer(divisor) != 0;
            1 <= to_integer(divisor);
            0 < 1;
            to_integer(value) < 1 * to_integer(divisor);
        };
        have truncating_quotient(to_integer(value), to_integer(divisor)) == 0 by {
            arithmetic_certificate {
                premise 0: truncating_quotient(to_integer(value), to_integer(divisor)) < 1 => truncating_quotient(to_integer(value), to_integer(divisor)) <= 0;
                premise 1: 0 <= truncating_quotient(to_integer(value), to_integer(divisor)) => 0 <= truncating_quotient(to_integer(value), to_integer(divisor));
                equal_from_bounds 0, 1 => truncating_quotient(to_integer(value), to_integer(divisor)) == 0;
                conclusion 2;
            }
        }
        apply(integer::truncation_identity(to_integer(value), to_integer(divisor))) using {
            to_integer(divisor) != 0;
        };
        have truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor) == 0 by {
            rewrite(truncating_quotient(to_integer(value), to_integer(divisor)) == 0);
            normalize();
        }
        have to_integer(value % divisor) == to_integer(value) by {
            arithmetic_certificate {
                premise 0: to_integer(value % divisor) == truncating_remainder(to_integer(value), to_integer(divisor)) => to_integer(value % divisor) == truncating_remainder(to_integer(value), to_integer(divisor));
                premise 1: to_integer(value) == truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor) + truncating_remainder(to_integer(value), to_integer(divisor)) => to_integer(value) == truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor) + truncating_remainder(to_integer(value), to_integer(divisor));
                premise 2: truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor) == 0 => truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor) == 0;
                scale 1 by -1 => -1 * to_integer(value) == -1 * (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor) + truncating_remainder(to_integer(value), to_integer(divisor)));
                add 0, 3 => to_integer(value % divisor) + -1 * to_integer(value) == truncating_remainder(to_integer(value), to_integer(divisor)) + -1 * (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor) + truncating_remainder(to_integer(value), to_integer(divisor)));
                scale 2 by -1 => -1 * (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) == -1 * 0;
                add 4, 5 => to_integer(value % divisor) + -1 * to_integer(value) + -1 * (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) == truncating_remainder(to_integer(value), to_integer(divisor)) + -1 * (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor) + truncating_remainder(to_integer(value), to_integer(divisor))) + -1 * 0;
                conclusion 6;
            }
        }
        assumption();
    }
}

// A native nonzero quotient guard bounds the exact Integer product.
theorem uint64_product_bound_from_division(x: uint64, y: uint64) {
    requires y != 0u64;
    requires x <= 18446744073709551615u64 / y;
    ensures to_integer(x) * to_integer(y) <= to_integer(18446744073709551615u64) by {
        have to_integer(y) != 0;
        have 0 <= to_integer(y);
        have 0 <= to_integer(18446744073709551615u64) by normalize();
        apply(integer::uint64_divide_to_integer(18446744073709551615u64, y)) using {
            y != 0u64;
            to_integer(y) != 0;
        };
        have to_integer(x) <= to_integer(18446744073709551615u64 / y);
        apply(integer::multiply_order_nonnegative(to_integer(x), to_integer(18446744073709551615u64 / y), to_integer(y))) using {
            to_integer(x) <= to_integer(18446744073709551615u64 / y);
            0 <= to_integer(y);
            y != 0u64;
        };
        apply(integer::truncation_identity(to_integer(18446744073709551615u64), to_integer(y))) using { to_integer(y) != 0; };
        apply(integer::nonnegative_dividend_remainder(to_integer(18446744073709551615u64), to_integer(y))) using {
            to_integer(y) != 0;
            0 <= to_integer(18446744073709551615u64);
        };
        have to_integer(18446744073709551615u64 / y) * to_integer(y) == truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)) * to_integer(y) by {
            rewrite(to_integer(18446744073709551615u64 / y) == truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)));
            normalize();
        }
        solve() using {
            to_integer(x) * to_integer(y) <= to_integer(18446744073709551615u64 / y) * to_integer(y);
            to_integer(18446744073709551615u64 / y) * to_integer(y) == truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)) * to_integer(y);
            to_integer(18446744073709551615u64) == truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)) * to_integer(y) + truncating_remainder(to_integer(18446744073709551615u64), to_integer(y));
            0 <= truncating_remainder(to_integer(18446744073709551615u64), to_integer(y));
        };
    }
}

// Representation bytes of one readable unsigned word, at the current point.
theorem uint32_from_le_bytes(p: uint32*) {
    requires little_endian();
    views p[0..1];
    requires defined(p[0]);
    ensures p[0] ==
        (((p as (uint8 *))[0] as uint32) |
         ((p as (uint8 *))[1] as uint32) << 8u32 |
         ((p as (uint8 *))[2] as uint32) << 16u32 |
         ((p as (uint8 *))[3] as uint32) << 24u32);
}
