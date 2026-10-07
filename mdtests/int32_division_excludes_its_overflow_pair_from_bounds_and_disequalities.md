# `int32` division is defined when the facts exclude `INT_MIN / -1`

The one signed overflow of an `int32` division or remainder is `INT_MIN / -1`.
`execute()` decides its overflow condition the way the `int64` twin in
[`int64_checked_scalar_arithmetic.md`](int64_checked_scalar_arithmetic.md)
does, from the operands: a divisor range without `-1`, on either side of it,
or a dividend range without `INT_MIN`, each read from that operand's own
indexed bounds and moved past the values its exact disequalities exclude; and
a recorded `y != -1` or `x != INT_MIN`, read directly, since `-1` lies inside
a divisor range where no endpoint walk reaches it. Each spelling below
excludes the pair and passes `execute()`.

The refusal that remains is
[`int32_division_by_a_nonzero_divisor_may_still_overflow.md`](int32_division_by_a_nonzero_divisor_may_still_overflow.md);
the exact exclusion stated as one disjunction is
[`int32_division_excluded_by_a_disjunction_is_defined.md`](int32_division_excluded_by_a_disjunction_is_defined.md).

```c filename=int32_division_excludes_its_overflow_pair.c
int32 positive_divisor(int32 x, int32 y) { return x / y; }
int32 negative_divisor(int32 x, int32 y) { return x / y; }
int32 divisor_not_minus_one(int32 x, int32 y) { return x / y; }
int32 dividend_not_int_min(int32 x, int32 y) { return x / y; }
int32 bounded_operands(int32 x, int32 y) { return x / y; }
int32 remainder(int32 x, int32 y) { return x % y; }
```

```click
verifying "int32_division_excludes_its_overflow_pair.c";

int32 positive_divisor(int32 x, int32 y) {
    requires y > 0;
    requires x >= 0;
    ensures result >= 0;
} by { execute(); simp(); }

int32 negative_divisor(int32 x, int32 y) {
    requires y < -1;
    ensures result == x / y;
} by { execute(); simp(); }

int32 divisor_not_minus_one(int32 x, int32 y) {
    requires y != 0;
    requires y != -1;
    ensures result == x / y;
} by { execute(); simp(); }

int32 dividend_not_int_min(int32 x, int32 y) {
    requires y != 0;
    requires x != -2147483647 - 1;
    ensures result == x / y;
} by { execute(); simp(); }

int32 bounded_operands(int32 x, int32 y) {
    requires 0 <= x and x <= 100;
    requires 1 <= y and y <= 100;
    ensures result == x / y;
} by { execute(); simp(); }

int32 remainder(int32 x, int32 y) {
    requires y > 0;
    ensures result == x % y;
} by { execute(); simp(); }
```

```expect
pass
```
