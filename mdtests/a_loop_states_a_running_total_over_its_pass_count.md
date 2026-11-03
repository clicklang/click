# A loop states a running total over its pass count

A loop's invariants can state its locals over `iterations`, the passes it has completed: 0 at entry, one more at each back edge.

```c filename=iter.c
int32 doubled(int32 n) {
    int32 i;
    int32 total;
    i = 0;
    total = 0;
    while (i < n) {
        total = total + 2;
        i = i + 1;
    }
    return total;
}
```

```click
verifying "iter.c";

int32 doubled(int32 n) {
    requires n >= 0 and n <= 1000;
    ensures result == 2 * n;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
        invariant i == iterations;
        invariant total == 2 * iterations;
    }
}
```

```expect
pass
```
