# A marked comparison does not hide a changed current pointer

One arm overwrites the current read with null while its marked value is
nonnull. The interface must reject that arm.

```c filename=probe.c
struct pair { struct pair *tag; int32 other; };
void put(struct pair *p, struct pair *q, int32 x) {
    struct pair *child = p->tag;
    if (x <= 0) { child->other = 0; } else { child->tag = 0; }
}
```

```click
verifying "probe.c";
void put(struct pair *p, struct pair *q, int32 x) {
    owns p->tag;
    requires p->tag == q;
    owns q->tag;
    owns q->other;
    requires q->tag != 0;
    ensures q->tag == old(q->tag);
} by {
    step(); step();
    mark before;
    branch ensuring {
        fact child->tag == at(before, child->tag);
    } then {
        step();
        have child->tag == at(before, child->tag) by { simp(); }
    } else {
        step();
    }
    execute(); simp();
}
```

```expect
fail: `branch ensuring` did not establish fact
```
