# A control owns an authority beside a named child

A control can own a population authority and a named child together. The
child's field is tied to the control's own field, and the control's fact
relates the population to C state. A member is created and spent while the
control is unfolded, and the population is retired at zero.

```c filename=authority_control_with_named_child.c
struct box { int32 used; int32 hits; };
int32 run() {
    struct box* b = malloc(sizeof(struct box));
    if (b == 0) return -1;
    b->used = 0;
    b->hits = 5;
    b->used = b->used + 1;
    b->used = b->used - 1;
    free(b);
    return 0;
}
```

```click
verifying "authority_control_with_named_child.c";

authorized resource ticket(b: struct box*) {}

resource hit_cell(b: struct box*) {
    field hits: int32;
    owns b->hits;
    fact b->hits == hits;
}

resource box_control(b: struct box*) {
    field hits: int32;
    owns b->used;
    owns stats: hit_cell(b);
    owns authority(ticket(b));
    fact stats.hits == hits;
    fact b->used == count(ticket(b));
}

int32 run() {
    ensures result == -1 or result == 0;
} by {
    step();
    step();
    branch then { step(); simp(); } else {}
    step();
    step();
    fold(authority(ticket(b)));
    let s = fold(hit_cell(b), { hits: 5 });
    let ctl = fold(box_control(b), { hits: 5 }, { stats: s });
    let { hits: hits, stats: s } = unfold(ctl);
    step();
    fold(ticket(b));
    let ctl = fold(box_control(b), { hits: hits }, { stats: s });
    let { hits: later_hits, stats: later } = unfold(ctl);
    unfold(ticket(b));
    step();
    unfold(later);
    have count(ticket(b)) == 0;
    unfold(authority(ticket(b)));
    step();
    step();
    simp();
}
```

```expect
pass
```
