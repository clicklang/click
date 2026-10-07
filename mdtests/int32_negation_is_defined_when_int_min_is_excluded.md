# `-x` is defined when `INT_MIN` is excluded, however that is spelled

Unary minus on `int32` lowers to `0 - x` and overflows at exactly one value,
`INT_MIN`. The subtraction's overflow decider ranges each operand and moves
the range past the values exact disequalities exclude, so `x != INT_MIN`
discharges it like the bound `x > INT_MIN` does. The refusal without either
is
[`int32_negation_without_a_bound_may_overflow.md`](int32_negation_without_a_bound_may_overflow.md).

```c filename=int32_negation_is_defined_when_int_min_is_excluded.c
int32 excluded(int32 x) { return -x; }
int32 above(int32 x) { return -x; }
```

```click
verifying "int32_negation_is_defined_when_int_min_is_excluded.c";

int32 excluded(int32 x) {
    requires x != -2147483647 - 1;
    ensures result == -x;
} by { execute(); simp(); }

int32 above(int32 x) {
    requires x > -2147483647 - 1;
    ensures result == -x;
} by { execute(); simp(); }
```

```expect
pass
```
