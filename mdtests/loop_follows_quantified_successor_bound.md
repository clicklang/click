# a loop follows a successor array whose quantified bound is invariant

`chase` replaces `cur` with `next[cur]` on every iteration and counts `i` up
to `n`. The loop never writes `next`, so the quantified invariant bounding every
`next` element holds at the back edge, and its instance at the old `cur`, whose
guard `0 <= cur and cur < n` the scalar invariants decide, bounds the new `cur`
when `close_invariants()` closes the loop. This catches a loop-closing order
search that drops a guarded quantified instance whose guard the context already
decides.

```c filename=loop_follows_quantified_successor_bound.c
int32 chase(int32 *next, int32 n) {
    int32 cur = 0;
    int32 i = 0;
    while (i < n) {
        cur = next[cur];
        i = i + 1;
    }
    return cur;
}
```

```click
verifying "loop_follows_quantified_successor_bound.c";

int32 chase(int32 *next, int32 n) {
    requires 1 <= n;
    views next[0..n];
    requires forall (k: int32) {
        0 <= k and k < n implies 0 <= next[k] and next[k] < n
    };
    ensures 0 <= result;
    ensures result < n;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        invariant 0 <= cur;
        invariant cur < n;
        invariant forall (k: int32) {
            0 <= k and k < n implies 0 <= next[k] and next[k] < n
        };
        views next[0..n];
        initialize by { simp(); }
        preserve by {
            have 0 <= next[cur] and next[cur] < n by {
                instantiate(forall (k: int32) {
                    0 <= k and k < n implies 0 <= next[k] and next[k] < n
                }, cur) using { 0 <= cur; cur < n; }
                assumption();
            }
            step();
            step();
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
