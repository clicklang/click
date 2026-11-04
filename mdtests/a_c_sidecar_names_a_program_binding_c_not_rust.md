# A C sidecar names a program binding c(name), not rust(name)

`rust(name)` is the Rust spelling of a program binding; a C source's is
`c(name)`.

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
        decreases n - rust(iterations);
        invariant 0 <= rust(iterations) and c(iterations) <= n;
        invariant rust(iterations) == iterations;
    }
    have loop(0).iterations == n by { solve(); }
}
```

```expect
fail: `rust(iterations)` names a Rust binding; a C or C++ source's is `c(iterations)`
```
