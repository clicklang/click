# A kept view of mixed-width owned fields is lent until released

`lend` views `*p` and produces `Lent(p)`, whose body keeps that view, so the
memory stays lent until `unlend` consumes it. The caller owns `*p` as three
pieces of different widths, `x` (8 bytes), `a` and `b` (4 each), which no
single owner covers: the planner joins them into one owner and lends that.
The fields keep their values across the lend, and after `unlend` the caller
owns them again, so `set_a` can write `a`.

```c filename=lend.c
struct S { long long x; int a; int b; };
void lend(const struct S* p);
void unlend(const struct S* p);
void set_a(struct S* p);
void keep(struct S* p) { lend(p); unlend(p); set_a(p); }
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
extern void set_a(struct S* p) {
    owns p->a;
    ensures p->a == 9;
}
void keep(struct S* p) {
    requires ((uint64)p & 7u64) == 0u64;
    owns p->x;
    owns p->a;
    owns p->b;
    ensures p->a == 9;
    ensures p->b == old(p->b);
    ensures p->x == old(p->x);
} by { execute(); simp(); }
```

```expect
pass
```
