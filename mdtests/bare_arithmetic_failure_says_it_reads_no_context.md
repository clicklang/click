# a failing `solve() using {}` says it reads no context

`solve() using {}` plans from the goal's own terms. The bound on
`x` below is in the context, but the empty list never reads it, so the step
fails. The failure says that no premises were listed and points at `using`,
rather than calling an empty list "the listed premises". Writing
`solve() using { 0 <= x; x <= 10; }` proves the same goal.

```click
theorem bare_arithmetic_reads_no_context(x: int32) {
    requires 0 <= x;
    requires x <= 10;
    ensures x + 1 <= 11 by {
        solve() using {};
    }
}
```

```expect
fail: `solve() using {}` reads no facts from the context, so list the facts the goal depends on in its `using { ... }`
```
