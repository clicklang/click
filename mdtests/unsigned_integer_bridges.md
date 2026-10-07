# Unsigned 64-bit Integer observation bridges

Unsigned arithmetic wraps. Exact observations of addition and multiplication
require a bound of UINT64_MAX; subtraction requires no underflow. Division
and remainder require native and observed nonzero divisor facts and use
mathematical truncation.

```click
theorem bridge0(left: uint64, right: uint64) {
    requires to_integer(left) + to_integer(right) <= 18446744073709551615;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by { apply(uint64_add_to_integer(left, right)); }
}
theorem bridge1(left: uint64, right: uint64) {
    requires to_integer(left) * to_integer(right) <= 18446744073709551615;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by { apply(uint64_multiply_to_integer(left, right)); }
}
theorem bridge2(left: uint64, right: uint64) {
    requires to_integer(right) <= to_integer(left);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by { apply(uint64_subtract_to_integer(left, right)); }
}
theorem bridge3(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right)) by { apply(uint64_divide_to_integer(left, right)); }
}
theorem bridge4(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right)) by { apply(uint64_remainder_to_integer(left, right)); }
}
theorem bridge5(left: uint64, right: uint64) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by { apply(uint64_less_equal_to_integer(left, right)); }
}
theorem bridge6(left: uint64, right: uint64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by { apply(uint64_less_equal_of_to_integer(left, right)); }
}
```

```expect
pass
```
