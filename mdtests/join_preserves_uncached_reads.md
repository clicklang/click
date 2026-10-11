# A join preserves unchanged uncached reads at both widths

The call establishes values through its contract. The branch changes only a
different field; read preservation must not depend on a cached cell.

```c filename=join_preserves_uncached_reads.c
struct pair { uint64 tag; int32 count; int32 left; };
void touch(struct pair *p) { p->tag = 42; p->count = 17; }
void keep(struct pair *p, int32 x) {
    touch(p);
    if (x <= 0) { p->left = 0; } else { p->left = 1; }
}
```

```click
verifying "join_preserves_uncached_reads.c";
void touch(struct pair* p) {
    requires p != 0;
    owns p->tag;
    owns p->count;
    ensures p->tag == 42;
    ensures p->count == 17;
} by { execute(); simp(); }
void keep(struct pair* p, int32 x) {
    requires p != 0;
    owns p->tag;
    owns p->count;
    owns p->left;
} by {
    step();
    have p->tag == 42 by { assumption(); }
    have p->count == 17 by { assumption(); }
    mark before_join;
    branch ensuring { fact 1 == 1; } then { step(); } else { step(); }
    have p->tag == 42 by { assumption(); }
    have p->count == 17 by { assumption(); }
    have p->tag == 42 by {
        transport(at(before_join, p->tag) == 42, p->tag == 42) using {
            at(before_join, p->tag) == 42;
        }
        assumption();
    }
    step();
    simp();
}
```

```expect
pass
```
