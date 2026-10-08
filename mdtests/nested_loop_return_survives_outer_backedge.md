# A nested loop return survives the outer back edge

An inner loop can return while another path continues through the outer
iteration. The outer loop must export that return with its own proof.

```c filename=nested_loop_return_survives_outer_backedge.c
int32 f(int32 n) {
    int32 i = 0;
    while (i < n) {
        int32 j = 0;
        while (j < 2) { if (i == 2) return 7; j++; }
        i = i + 1;
    }
    return i;
}
```

```click
verifying "nested_loop_return_survives_outer_backedge.c";

int32 f(int32 n) {
    requires n == 5;
    ensures result == 5 or result == 7;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0;
        invariant i <= n;
        preserve by {
            step(); step();
            loop { decreases 2-j; invariant j >= 0; invariant j <= 2; invariant i >= 0; invariant i < n; }
            step();
            simp();
        }
    }
    step();
    have result == 5 by simp;
    simp();
}
```

```expect
pass
```
