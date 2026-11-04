# A C local named iterations is written c(iterations)

In a loop's clauses and phases, bare `iterations` is the pass count; a C
local of that name is `c(iterations)`, and both can be stated together.

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
        decreases n - c(iterations);
        invariant 0 <= c(iterations) and c(iterations) <= n;
        invariant c(iterations) == iterations;
    }
    have loop(0).iterations == n by { solve(); }
}
```

```expect
pass
```
