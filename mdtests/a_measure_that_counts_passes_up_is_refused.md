# A measure that counts passes up is refused

`decreases iterations` grows by one each pass, so its descent member is refused.

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
        decreases iterations;
        invariant 0 <= i and i <= n;
        invariant i == iterations;
        invariant total == 2 * iterations;
    }
}
```

```expect
fail: `iterations` decreases at the back edge
```
