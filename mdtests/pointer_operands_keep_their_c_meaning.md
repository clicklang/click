# Pointer locals, fields and results keep their C meaning

Specification arithmetic compares exact Integers, but arithmetic on a
pointer is C pointer arithmetic, so a comparison with a pointer among its
arithmetic operands keeps its C meaning. That holds for a pointer-typed
struct field (`s->p`), a pointer `result`, and a pointer local (`q`), as it
does for a pointer parameter.

```c filename=advance.c
struct S { int *p; };
int *advance(struct S *s, int n) {
    int *q = s->p;
    q = q + n;
    return q;
}
```

```click
verifying "advance.c";

int32* advance(struct S* s, int32 n) {
    views s->p;
    views s->p[0..4];
    requires 0 <= n and n <= 4;
    ensures result == s->p + n;
} by {
    step(); step(); step();
    have q == s->p + n by solve();
}
```

```expect
pass
```
