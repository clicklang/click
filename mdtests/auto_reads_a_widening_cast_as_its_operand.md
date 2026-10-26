# The implicit closer reads a widening cast as its operand

A widening cast keeps its value (`design/machine-integers.md`, conversion
table), so the implicit closer proves the observation of each 32-to-64-bit widening equal
to its operand's, from the operand's type range. With that identity it closes
a widened sum's guard from the Integer bound of the narrow sum.

```click
theorem int32_to_int64(a: int32) {
    ensures to_integer(a as int64) == to_integer(a);
}

theorem uint32_to_int64(a: uint32) {
    ensures to_integer(a as int64) == to_integer(a);
}

theorem uint32_to_uint64(a: uint32) {
    ensures to_integer(a as uint64) == to_integer(a);
}

theorem widened_sum_guard(a: uint32, b: uint32) {
    requires to_integer(a) + to_integer(b) <= 4294967295;
    ensures to_integer(a as int64 + b as int64) <= to_integer(4294967295i64);
}

theorem widened_native_sum_guard(a: uint32, b: uint32) {
    requires to_integer(a) + to_integer(b) <= 4294967295;
    ensures a as int64 + b as int64 <= 4294967295i64;
}
```

```expect
pass
```
