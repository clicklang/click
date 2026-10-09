# An interface compares a current pointer read with a proof mark

A mixed comparison is state-parametric on its current side. Treating any
mention of a proof mark as wholly historical skipped the interface certificate
and made the kernel reject the join after both arms had proved the fact.

```c filename=probe.c
struct pair { struct pair *tag; int32 other; };
void put(struct pair *p, struct pair *q, int32 x) {
    struct pair *child = p->tag;
    if (x <= 0) { child->other = 0; } else { child->other = 1; }
}
```

```click
verifying "probe.c";
void put(struct pair *p, struct pair *q, int32 x) {
    owns p->tag;
    requires p->tag == q;
    owns q->tag;
    owns q->other;
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
        have child->tag == at(before, child->tag) by { simp(); }
    }
    execute(); simp();
}
```

```expect
pass
```
