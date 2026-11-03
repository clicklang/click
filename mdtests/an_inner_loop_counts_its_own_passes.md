# An inner loop counts its own passes

Inside a nested loop `iterations` is that loop's count; past it, the outer proof reads it as `loop(1).iterations`.

```c filename=nest.c
int32 grid(int32 n) {
    int32 i;
    int32 j;
    i = 0;
    j = 0;
    while (i < n) {
        j = 0;
        while (j < n) {
            j = j + 1;
        }
        i = i + 1;
    }
    return i;
}
```

```click
verifying "nest.c";

int32 grid(int32 n) {
    requires n >= 1 and n <= 100;
    ensures result == n;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
        invariant i == iterations;
        invariant 0 <= j and j <= n;
        preserve by {
            step();
            loop {
                decreases n - j;
                invariant 0 <= j and j <= n;
                invariant j == iterations;
            }
            have loop(1).iterations == to_integer(n) by { solve(); }
        }
    }
    have loop(0).iterations == to_integer(n) by { solve(); }
}
```

```expect
pass
```
