# a failing bare arithmetic says it reads no context

`arithmetic()` without `using` plans from the goal's own terms. The bound on
`x` below is in the context, but the bare form never reads it, so the step
fails. The failure says that no premises were listed and points at `using`,
rather than calling an empty list "the listed premises". Writing
`arithmetic() using { 0 <= x; x <= 10; }` proves the same goal.

```click
theorem bare_arithmetic_reads_no_context(x: int32) {
    requires 0 <= x;
    requires x <= 10;
    ensures x + 1 <= 11 by {
        arithmetic();
    }
}
```

```expect
fail: `arithmetic()` without `using` reads no facts from the context, so list the facts the goal depends on with `using { ... }`
```
