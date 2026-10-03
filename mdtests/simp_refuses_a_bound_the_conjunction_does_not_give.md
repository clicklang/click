# simp refuses a bound the conjunction does not give

The negative of
`mdtests/simp_reads_a_bound_inside_a_requires_conjunction.md`: the
conjunction's bounds put `x + 1` in `[1, 101]`, which does not give
`result >= 2`, so no extracted conjunct closes the goal.

```c filename=simp_refuses_a_bound_the_conjunction_does_not_give.c
int32 inc(int32 x) {
    return x + 1;
}
```

```click
verifying "simp_refuses_a_bound_the_conjunction_does_not_give.c";

int32 inc(int32 x) {
    requires x >= 0 and x <= 100;
    ensures result >= 2;
} by { execute(); simp(); }
```

```expect
fail: unclosed goal
```
