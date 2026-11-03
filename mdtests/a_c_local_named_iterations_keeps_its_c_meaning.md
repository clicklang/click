# A C local named iterations keeps its C meaning

A C object named `iterations` is what the loop clauses read by that name; the
loop's pass count then has no bare spelling there.

```c filename=named.c
int32 count(int32 n) {
    int32 iterations;
    iterations = 0;
    while (iterations < n) {
        iterations = iterations + 1;
    }
    return iterations;
}
```

```click
verifying "named.c";

int32 count(int32 n) {
    requires n >= 0 and n <= 1000;
    ensures result == n;
} by {
    step();
    step();
    loop {
        decreases n - iterations;
        invariant 0 <= iterations and iterations <= n;
    }
}
```

```expect
pass
```
