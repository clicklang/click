# An unsigned remainder by a divisor that may be zero is not bounded

A remainder by a nonzero divisor is at most its dividend; with only
`0u64 < b` known it is. With nothing known about `b`, `a % b` may be the
opaque `a % 0u64`, which bounds nothing.

```click
theorem bounded(a: uint64, b: uint64) {
    requires 0u64 < b;
    ensures a % b <= a;
}

theorem unbounded(a: uint64, b: uint64) {
    ensures a % b <= a;
}
```

```expect
fail: could not establish `(a % b) <= a`
```
