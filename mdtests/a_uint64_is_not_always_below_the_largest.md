# A uint64 is not always below the largest

`value <= 18446744073709551614u64` is false when `value` is the largest
`uint64`, so it does not hold with no facts and `normalize` refuses it.

`every_uint64_is_at_most_the_largest.md` has the bound that does hold.

```click
theorem below_top(value: uint64) {
    ensures value <= 18446744073709551614u64 by {
        normalize();
    }
}
```

```expect
fail: did not normalize to true
```
