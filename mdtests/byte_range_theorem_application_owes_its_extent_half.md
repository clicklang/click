# Applying a theorem over a byte range owes the range's extent half

The negative of `byte_range_theorem_carries_its_extent_half.md`. A theorem
whose premise is a `uint8` range assumes the range's extent half, so applying
it owes that half: citing the range adds it only where it is an available
fact. Here the cited range `v[lo..k]` was narrowed to, not stated, so
`0 <= k - lo` is a fact nobody established and the application is refused
naming it. Were the half not owed, the theorem would hand back
`0 <= k - lo` where `lo <= k` holds but `k - lo` exceeds `2147483647` bytes
and is negative as a signed count.

Integer arithmetic reads `0 <= hi - lo` as an Integer claim, so the native half
is written as its exact observation `0 <= to_integer(hi - lo)`, which names
`hi - lo` only where it is defined; each theorem requires `defined(hi - lo)`.

```click
theorem stated_byte_range_extent_is_nonnegative(v: uint8[], lo: int32, hi: int32) {
    views v[lo..hi];
    requires defined(hi - lo);
    ensures 0 <= to_integer(hi - lo) by assumption();
}

theorem narrowed_byte_range_owes_its_extent(v: uint8[], lo: int32, n: int32, k: int32) {
    views v[lo..n];
    requires lo <= k;
    requires k <= n;
    requires defined(k - lo);
    ensures 0 <= to_integer(k - lo) by {
        have viewable(v[lo..k]);
        apply(stated_byte_range_extent_is_nonnegative(v, lo, k)) using {
            viewable(v[lo..k]);
            defined(k - lo);
        };
    }
}
```

```expect
fail: `0 <= to_integer(k - lo)` is not an available fact
```
