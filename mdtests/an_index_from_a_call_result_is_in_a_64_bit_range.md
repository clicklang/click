# An index from a call result is in a 64-bit range

`through` reads the last element at `n - 1`, where `n` is what `size`
returned. The range is bounded by the field `s->n`, and `size`'s contract
says its result is that field. The access is placed in the range by
comparing `n - 1` with the bound in the bound's own spelling: the two are
equal, so `n - 1 < s->n` is `s->n - 1 < s->n`, which holds when
`1 <= s->n`. `std::span::back()` has this shape.

`direct` reads the field itself.

`an_index_from_a_call_result_needs_a_nonempty_range.md` leaves out the
requirement.

```c filename=an_index_from_a_call_result_is_in_a_64_bit_range.c
struct S { int *p; unsigned long n; };
unsigned long size(const struct S *s) { return s->n; }
int direct(const struct S *s) { return s->p[s->n - 1]; }
int through(const struct S *s) { unsigned long n = size(s); int *q = s->p; return q[n - 1]; }
```

```click
verifying "an_index_from_a_call_result_is_in_a_64_bit_range.c";
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
    requires 1u64 <= s->n;
    ensures result == old(s->p[s->n - 1u64]);
} by { execute(); simp(); }
```

```expect
pass
```
