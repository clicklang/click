# A kept view of owned fields with a gap is refused

The caller owns `x` and `b` but not `a`, so its pieces do not cover `*p`
and there is nothing to lend for the view `Lent(p)` keeps.

```c filename=lend.c
struct S { long long x; int a; int b; };
void lend(const struct S* p);
void unlend(const struct S* p);
void keep(struct S* p) { lend(p); unlend(p); }
```

```click
verifying "lend.c";
resource Lent(p: struct S*) { views *p; }
extern void lend(const struct S* p) {
    views *p;
    produces Lent(p);
}
extern void unlend(const struct S* p) {
    consumes Lent(p);
}
void keep(struct S* p) {
    requires ((uint64)p & 7u64) == 0u64;
    owns p->x;
    owns p->b;
    ensures p->b == old(p->b);
} by { execute(); simp(); }
```

```expect
fail: stable-view the required loan backing or binding is missing refused during planning
```
