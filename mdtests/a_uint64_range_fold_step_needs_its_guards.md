# A uint64 range fold step needs its guards

The append law for a `uint64` range adds the element at `hi` to the fold
up to `hi`. It holds when `lo <= hi`, so the shorter range is not past its
end, and when `hi` is below the largest `uint64`, so `hi + 1` does not
wrap to zero and name the empty range. With the second guard left out
`peel` is refused, naming it.

`a_range_fold_over_uint64.md` lists both.

```click
function total(lo: uint64, hi: uint64) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(k) })
}

theorem step(lo: uint64, hi: uint64) {
    requires lo <= hi;
    ensures total(lo, hi + 1u64) == total(lo, hi) + to_integer(hi) by {
        peel(total(lo, hi + 1u64)) using { lo <= hi; }
        simp();
    }
}
```

```expect
fail: the append-last-cell equation needs `hi < 18446744073709551615u64`
```
