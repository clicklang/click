# simp reads a bound from a negated branch condition

On the fall-through path of `if (x > 100) return 0;` the path fact is
`x > 100` is false. Simp reads it from `x`'s indexed bound bucket as the
upper bound `x <= 100`, which with `x >= 0` keeps `x + 1` in range, so the
whole function closes with `execute(); simp();` and no hand-written branch.

```c filename=simp_reads_a_bound_from_a_negated_branch_condition.c
int32 add_one(int32 x) {
    if (x > 100) {
        return 0;
    }
    return x + 1;
}
```

```click
verifying "simp_reads_a_bound_from_a_negated_branch_condition.c";

int32 add_one(int32 x) {
    requires x >= 0;
    ensures result >= 0;
    ensures result <= 101;
} by { execute(); simp(); }
```

```expect
pass
```
