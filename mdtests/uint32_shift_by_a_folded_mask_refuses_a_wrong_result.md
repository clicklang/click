# A folded unsigned shift refuses an incorrect result

```click
theorem cast_shift(x: uint64) {
    requires x == 1753877967969059832u64;
    ensures (182457789u32 << ((0u32 - (x >> 59u64) as uint32) & 31u32)) == 2684354561u32 by {
        rewrite(x, 1753877967969059832u64);
        close();
    }
}
```

```expect
fail: could not establish `(2684354560 : Integer) == 2684354561`
```
