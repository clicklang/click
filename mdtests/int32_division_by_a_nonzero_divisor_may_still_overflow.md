# A nonzero `int32` divisor alone leaves `INT_MIN / -1` open

`y != 0` excludes the zero divisor and nothing else: `INT_MIN / -1` stays
reachable, and the refusal names that one operand pair rather than a bare
`signed overflow`. The spellings that do exclude it are in
[`int32_division_excludes_its_overflow_pair_from_bounds_and_disequalities.md`](int32_division_excludes_its_overflow_pair_from_bounds_and_disequalities.md).

```c filename=int32_division_by_a_nonzero_divisor.c
int32 quotient(int32 x, int32 y) { return x / y; }
```

```click
verifying "int32_division_by_a_nonzero_divisor.c";

int32 quotient(int32 x, int32 y) {
    requires y != 0;
    ensures result == x / y;
} by { execute(); simp(); }
```

```expect
fail: undefined behavior: signed overflow (INT_MIN / -1
```
