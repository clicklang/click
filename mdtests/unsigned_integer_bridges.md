# Unsigned Integer observation bridges

Unsigned arithmetic wraps. Exact observations of addition and multiplication
require a bound of the type's maximum; subtraction requires no underflow.
`auto` reads the sum and difference identities by one rule at every width, so
the `uint32` ones close as the `uint64` ones do. Division
and remainder require native and observed nonzero divisor facts and use
mathematical truncation.

```click
import click::integer;

theorem bridge0(left: uint64, right: uint64) {
    requires to_integer(left) + to_integer(right) <= 18446744073709551615;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by auto();
}
theorem bridge1(left: uint64, right: uint64) {
    requires to_integer(left) * to_integer(right) <= 18446744073709551615;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by apply(uint64_multiply_to_integer(left, right));
}
theorem bridge2(left: uint64, right: uint64) {
    requires to_integer(right) <= to_integer(left);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by auto();
}
theorem bridge3(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right)) by apply(uint64_divide_to_integer(left, right));
}
theorem bridge4(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right)) by apply(uint64_remainder_to_integer(left, right));
}
theorem bridge5(left: uint64, right: uint64) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by auto();
}
theorem bridge6(left: uint64, right: uint64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by auto();
}
theorem bridge0_uint32(left: uint32, right: uint32) {
    requires to_integer(left) + to_integer(right) <= 4294967295;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by auto();
}
theorem bridge2_uint32(left: uint32, right: uint32) {
    requires to_integer(right) <= to_integer(left);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by auto();
}
```

```expect
pass
```
