# The exact exclusion `x != INT_MIN or y != -1` defines an `int32` division

`INT_MIN / -1` is one operand pair, so the weakest fact that excludes it is
the disjunction `x != INT_MIN or y != -1`. `requires` and `have` record such
a disjunction whole, as one proposition fact; the overflow decider reads it
with a keyed lookup of that fact in either arm order, with no case split. The
other spellings are in
[`int32_division_excludes_its_overflow_pair_from_bounds_and_disequalities.md`](int32_division_excludes_its_overflow_pair_from_bounds_and_disequalities.md).

```c filename=int32_division_excluded_by_a_disjunction.c
int32 required(int32 x, int32 y) { return x / y; }
int32 established(int32 x, int32 y) { return x / y; }
```

```click
verifying "int32_division_excluded_by_a_disjunction.c";

int32 required(int32 x, int32 y) {
    requires y != 0;
    requires x != -2147483647 - 1 or y != -1;
    ensures result == x / y;
} by { execute(); simp(); }

int32 established(int32 x, int32 y) {
    requires 0 <= x and x <= 100;
    requires 1 <= y and y <= 100;
    ensures result == x / y;
} by {
    have y != 0;
    have x != -2147483647 - 1 or y != -1;
    execute();
    simp();
}
```

```expect
pass
```
