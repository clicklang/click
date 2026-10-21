# A theorem's byte range carries its extent half

A stated range carries its extent half beside its viewability half, and a
range of one-byte elements is no exception: `views v[lo..hi]` over `uint8`
states `0 <= hi - lo` as well. It lowers its extent unscaled, `hi - lo` bytes
rather than `(hi - lo) * 1`, and the rule that recovers a stated range's
extent guards from its lowered proposition read the element width off the
scale factor, so a byte range carried no extent half: the first theorem could
not see `0 <= hi - lo`. Its application owes that half as well, and listing
the range cites it from the applying theorem's own `views` clause.

Integer arithmetic reads `0 <= hi - lo` as an Integer claim, so the native half
is written as its exact observation `0 <= to_integer(hi - lo)`, which names
`hi - lo` only where it is defined; each theorem requires `defined(hi - lo)`.

```click
theorem stated_byte_range_extent_is_nonnegative(v: uint8[], lo: int32, hi: int32) {
    views v[lo..hi];
    requires defined(hi - lo);
    ensures 0 <= to_integer(hi - lo) by assumption();
}

theorem apply_cites_the_byte_range_extent(v: uint8[], lo: int32, hi: int32) {
    views v[lo..hi];
    requires defined(hi - lo);
    ensures 0 <= to_integer(hi - lo) by {
        apply(stated_byte_range_extent_is_nonnegative(v, lo, hi)) using {
            viewable(v[lo..hi]);
            defined(hi - lo);
        };
    }
}
```

```expect
pass
```
