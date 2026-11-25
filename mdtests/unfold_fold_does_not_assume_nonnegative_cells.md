# Unfolding a fold does not assume its cells are nonnegative

The available range conditions select the append law and ordinary obligations
handle its arithmetic guards. They do not establish that the array's arbitrary
values, or their sum, are nonnegative. The final claim must still be refused.

```click
function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

theorem icount_needs_a_range_guard(p: int32[], lo: int32, hi: int32) {
    requires 0 < hi;
    requires to_integer(lo) <= to_integer(hi - 1);
    requires hi >= 0 and viewable(p[lo..hi]);
    ensures 0 <= icount(p, lo, hi) by {
        unfold(icount(p, lo, hi));
        close();
    }
}
```

```expect
fail: could not establish `0 <= ((icount(p, lo, (hi - 1)) + to_integer(p[((hi - 1) as int32)])) : Integer)`
```
