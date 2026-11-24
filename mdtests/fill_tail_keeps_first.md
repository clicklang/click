# fill_tail keeps the first cell with an old-state invariant

This checks that a pointer-writing loop can prove an old-memory theorem when
the unchanged-memory fact is stated explicitly as a loop invariant. The loop
writes `p[i]` for `1 <= i < n`, so the invariant proves `p[0]` is unchanged.

```c filename=fill_tail_keeps_first.c
int32 fill_tail_keeps_first(int32 p[], int32 n) {
    int32 i;
    i = 1;
    while (i < n) {
        p[i] = i;
        i = i + 1;
    }
    return i;
}
```

```click
verifying "fill_tail_keeps_first.c";

int32 fill_tail_keeps_first(int32 p[], int32 n) {
    requires n >= 1 and n <= 2147483647;
    consumes p[0..n];
    ensures frame_and_result: p[0] == old(p[0]) and result == n;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 1 and i <= n;
        invariant p[0] == old(p[0]);
        maintain by {
            mark before_store;
            have i != 0 by { close() using { i >= 1; }; }
            have separate(memory(p[i]), memory(p[0])) by {
                apply(click::separation::separate_elements(p, i, 0));
            }
            step();
            have at(before_store, separate(statement(2).statement(0).footprint, memory(p[0]))) by {
                known();
            }
            have p[0] == at(before_store, p[0]) by {
                preserve(at(before_store, memory(p[0])), statement(2).statement(0));
            }
            have p[0] == old(p[0]) by { known(); }
            step();
        }
    }
    step();
    solve();
}
```

```expect
pass
```
