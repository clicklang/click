# Writing a field while its kept view is lent is refused

While `Lent(p)` keeps `*p` lent, the joined owner of `x`, `a` and `b` is
suspended, so the store `p->a = 2` before `unlend` finds only a view.

```c filename=lend.c
struct S { long long x; int a; int b; };
void lend(const struct S* p);
void unlend(const struct S* p);
void keep(struct S* p) { p->a = 1; lend(p); p->a = 2; unlend(p); }
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
    owns p->a;
    owns p->b;
    ensures p->a == 2;
} by { execute(); simp(); }
```

```expect
fail: missing resource fact `owns p->a`
```
