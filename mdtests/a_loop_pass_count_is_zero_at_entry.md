# A loop pass count is zero at entry

The entry checks the invariants with `iterations` at 0, so an invariant that needs another count there is refused.

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
        invariant i + 1 == iterations;
        invariant total == 2 * i;
    }
}
```

```expect
fail: loop initialization body did not close its goal
```
