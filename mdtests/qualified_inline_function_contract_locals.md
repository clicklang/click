# Qualified contracts use the selected inline function's local pointer types

```c filename=first.c
struct box { int pad; unsigned long wide; };
static inline unsigned long helper(struct box *p) {
    struct box *q = p;
    return q->wide;
}
unsigned long run(struct box *p) { return helper(p); }
```

```c filename=second.c
struct box { int pad; unsigned long wide; };
static inline unsigned long helper(struct box *p) {
    struct box *q = p;
    return q->wide;
}
unsigned long other(struct box *p) { return helper(p); }
```

```click
verifying "first.c" as first;
verifying "second.c" as second;
unsigned long first::helper(struct box* p) {
    owns p->wide;
    ensures result == old(p->wide);
} by {
    step(); step();
    have q->wide == old(p->wide) by { simp(); }
    execute(); simp();
}
unsigned long run(struct box* p) {
    owns p->wide;
    ensures result == old(p->wide);
} by { execute(); simp(); }
```

```expect
pass
```
