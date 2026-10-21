# a fold law is refused when the endpoint is not known to be defined

This is the same append-law application with `0 < hi` removed. Nothing then
decides that `hi - 1` is defined, so its exact observation `to_integer(hi - 1)`
is refused where the first requirement states it. The refusal names the
offending subterm and the condition that is missing.

```click
theorem fold_rejects_an_undefined_endpoint(lo: int32, hi: int32) {
    requires to_integer(lo) <= to_integer(hi - 1);
    requires to_integer(hi - 1) < 2147483647;
    ensures (lo..((hi - 1) + 1)).fold(0, |acc, k| { acc + to_integer(k) }) ==
        (lo..(hi - 1)).fold(0, |acc, k| { acc + to_integer(k) }) +
            to_integer(hi - 1) by {
        apply(integer_range_fold_append(
            (lo..(hi - 1)).fold(0, |acc, k| { acc + to_integer(k) })
        )) using {
            to_integer(lo) <= to_integer(hi - 1);
            to_integer(hi - 1) < 2147483647;
        };
    }
}
```

```expect
fail: not established: `hi - 1` must not overflow
```
