# `-x` without a bound may overflow

Nothing excludes `x == INT_MIN`, so `-x` keeps its undefined path. The
spellings that exclude it are in
[`int32_negation_is_defined_when_int_min_is_excluded.md`](int32_negation_is_defined_when_int_min_is_excluded.md).

```c filename=int32_negation_without_a_bound.c
int32 negate(int32 x) { return -x; }
```

```click
verifying "int32_negation_without_a_bound.c";

int32 negate(int32 x) {
    ensures result == -x;
} by { execute(); simp(); }
```

```expect
fail: undefined behavior: signed overflow
```
