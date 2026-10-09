# An index from a call result needs a nonempty range

`through` of `an_index_from_a_call_result_is_in_a_64_bit_range.md` without
`requires 1u64 <= s->n`. With an empty range `n - 1` wraps to the largest
`uint64`, which is not below the bound, so the read is refused.

```c filename=an_index_from_a_call_result_needs_a_nonempty_range.c
struct S { int *p; unsigned long n; };
unsigned long size(const struct S *s) { return s->n; }
int direct(const struct S *s) { return s->p[s->n - 1]; }
int through(const struct S *s) { unsigned long n = size(s); int *q = s->p; return q[n - 1]; }
```

```click
verifying "an_index_from_a_call_result_needs_a_nonempty_range.c";
uint64 size(const struct S* s) {
    views s->n;
    ensures result == s->n;
} by { execute(); simp(); }
int32 direct(const struct S* s) {
    views s->p;
    views s->n;
    views s->p[0..s->n];
    requires 1u64 <= s->n;
    ensures result == old(s->p[s->n - 1u64]);
} by { execute(); simp(); }
int32 through(const struct S* s) {
    views s->p;
    views s->n;
    views s->p[0..s->n];
    ensures result == old(s->p[s->n - 1u64]);
} by { execute(); simp(); }
```

```expect
fail: missing resource fact
```
