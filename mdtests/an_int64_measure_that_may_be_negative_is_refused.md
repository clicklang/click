# An int64 measure that may be negative is refused

A signed measure owes its lower bound at the back edge: descent through
negative values is not well founded. `count` steps `i` by two while
`i < length`, so the last step can take `i` past `length` and the measure
`length - i` to `-1`. No invariant rules that out, and the loop is refused at
the member `0 <= length - i` of the incremented counter.

The loop of `a_long_loop_is_ranked_by_an_int64_measure.md`, whose guard
`i + 1 < length` keeps `i + 2 <= length`, owes the same member and proves it.

```c filename=an_int64_measure_that_may_be_negative_is_refused.c
long count(long length) {
    long i = 0;
    while (i < length) {
        i += 2;
    }
    return i;
}
```

```click
verifying "an_int64_measure_that_may_be_negative_is_refused.c";

int64 count(int64 length) {
    requires 0i64 <= length;
    requires length <= 2147483647i64;
    ensures result >= length;
} by {
    execute_until(loop(0));
    loop {
        decreases length - i;
        invariant 0i64 <= i;
        invariant i <= 2147483647i64;
    }
    execute(); solve();
}
```

```expect
fail: closure body did not prove every invariant obligation
```
