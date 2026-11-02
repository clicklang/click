# A loop binder is rebound by its arguments, not by the body's name

The body folds its result under a new name, `d`. The back edge selects the
loop binder the same way the head did — the one owned `counter(p)` — so `c`
names the instance the body called `d`, and the invariants are checked against
that instance's fresh model. No binder map is written anywhere.

The head's model `c.count` is an arbitrary value of its own, so before touching
the cell the body states what the invariants make it: `c.count == i`. Nothing
else bounds the cell that the increment writes.

```c filename=loop_binder_rebinds_by_arguments.c
struct cell { int32 value; };

void bump_n(struct cell* p, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        p->value = p->value + 1;
        i = i + 1;
    }
}
```

```click
verifying "loop_binder_rebinds_by_arguments.c";

resource counter(p: struct cell*) {
    field count: int32;
    owns p->value;
    fact p->value == count;
}

void bump_n(struct cell* p, int32 n) {
    requires n >= 0;
    requires n <= 1000;
    owns c: counter(p);
    requires c.count == 0;
    ensures to_integer(c.count) == to_integer(old(c.count) + n);
} by {
    step();
    step();
    loop {
        decreases n - i;
        owns c: counter(p);
        invariant i >= 0;
        invariant i <= n;
        invariant to_integer(c.count) == to_integer(old(c.count) + i);

        initialize by solve();
        preserve by {
            have c.count == i by {
                rewrite(to_integer(c.count) == to_integer((old(c.count) + i)));
                rewrite(old(c.count) == 0);
                normalize();
            }
            unfold(c);
            step();
            step();
            let d = fold(counter(p), { count: (old(c.count) + i) });
        }
    }
    have i == n;
}
```

```expect
pass
```
