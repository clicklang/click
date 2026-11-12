# A bound and a disequality give a strict 64-bit bound

A search over a `size_t` range stops before its end: under `lo <= hi` and
`lo != hi`, the next probe `lo` is below `hi`. `solve` makes the bound strict
by the Integer certificate's `less_than_from_not_equal`, which cites the
disequality of the bound's own difference, at every format and over
`Integer`; before, only the `signed_int32` certificate had the step, so this
held at `int32` alone (`width_uniformity.rs`, the
`less_equal_and_not_equal_implies_less_than` family). A disequality of
another difference gives nothing, and the second function is refused.

```c filename=probe.c
uint64_t probe(uint64_t lo, uint64_t hi) {
    return lo;
}

uint64_t probe_unrelated(uint64_t lo, uint64_t hi, uint64_t other) {
    return lo;
}
```

```click
verifying "probe.c";

uint64 probe(uint64 lo, uint64 hi) {
    requires lo <= hi;
    requires lo != hi;
    ensures result < hi;
}

uint64 probe_unrelated(uint64 lo, uint64 hi, uint64 other) {
    requires lo <= hi;
    requires lo != other;
    ensures result < hi;
}
```

```expect
fail: probe_unrelated
```
