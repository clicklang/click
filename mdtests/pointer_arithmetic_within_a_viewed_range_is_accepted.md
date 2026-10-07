# Pointer arithmetic inside a viewed range of a parameter is accepted

The positive companion to
`pointer_arithmetic_past_a_viewed_range_is_refused.md`. The one-past end of
the held range is a valid address, displacing by zero is always fine, and a
symbolic displacement is accepted when the facts place it inside the range,
end included. None of the formed pointers is dereferenced.

```c filename=pointer_arithmetic_within_a_viewed_range_is_accepted.c
int32 one_past_end(int32 *p) { int32 *q = p + 4; return q != p; }

int32 displaced_by_zero(int32 *p) { int32 *q = p + 0; return q == p; }

int32 inside_by_facts(int32 *p, int32 i) { int32 *q = p + i; return q == p + i; }
```

```click
verifying "pointer_arithmetic_within_a_viewed_range_is_accepted.c";

int32 one_past_end(int32 *p) {
    views p[0..4];
    ensures result == 1;
} by { execute(); simp(); }

int32 displaced_by_zero(int32 *p) {
    views p[0..4];
    ensures result == 1;
} by { execute(); simp(); }

int32 inside_by_facts(int32 *p, int32 i) {
    requires 0 <= i and i <= 4;
    views p[0..4];
    ensures result == 1;
} by { execute(); simp(); }
```

```expect
pass
```
