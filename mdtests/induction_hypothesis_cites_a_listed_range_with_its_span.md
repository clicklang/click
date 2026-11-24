# An induction hypothesis's range premise is cited with its span halves

The hypothesis `let ih = induct(hi)` gives is the theorem's own statement at the
smaller argument, and that statement includes the span halves of every range
it names: the theorem's proof assumed them, so a use of the theorem, including
a use by its own induction, owes them.

The range here does not move with the induction variable, so the halves the
hypothesis owes, `0 <= n - lo` and `n - lo <= 1073741823`, are the theorem's
own, available beside the stated range. Both induction and theorem application
can use the range and its span facts from scope. The negative,
where a moved range's halves are not available, is
`induction_hypothesis_owes_the_range_span.md`.

Integer arithmetic reads `0 <= n - lo` as an Integer claim, so the native half
is written as its exact observation `0 <= to_integer(n - lo)`, which names
`n - lo` only where it is defined; each theorem requires `defined(n - lo)`.

```click
theorem hypothesis_cites_the_range_span(v: int32[], lo: int32, n: int32, hi: int32) {
    requires 0 <= lo;
    requires 0 <= hi;
    requires hi <= n;
    requires n >= 0 and viewable(v[lo..n]);
    ensures 0 <= hi by {
        let ih = induct(hi);
        if hi <= 0 {
            close();
        } else {
            have 0 < hi;
            have 0 <= to_integer(hi - 1) by { close() using { 0 < hi; }; }
            have to_integer(hi - 1) < to_integer(hi) by { close() using { 0 < hi; }; }
            have to_integer(hi - 1) <= to_integer(n) by { close() using { 0 < hi; hi <= n; }; }
            apply(ih(hi - 1));
            close();
        }
    }
}

theorem stated_range_span_is_nonnegative(v: int32[], lo: int32, n: int32) {
    views v[lo..n];
    requires defined(n - lo);
    ensures 0 <= to_integer(n - lo) by close();
}

theorem apply_cites_the_range_span(v: int32[], lo: int32, n: int32) {
    views v[lo..n];
    requires defined(n - lo);
    ensures 0 <= to_integer(n - lo) by {
        apply(stated_range_span_is_nonnegative(v, lo, n));
    }
}
```

```expect
pass
```
