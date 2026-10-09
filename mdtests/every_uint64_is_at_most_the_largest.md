# Every uint64 is at most the largest

`value <= 18446744073709551615u64` holds for every `uint64`, as
`0u64 <= value` does, and `normalize` closes both with no facts. The upper
one was left open, which is what `uint64_to_integer_bounds` rests on.

`a_uint64_is_not_always_below_the_largest.md` lowers the bound by one.

```click
theorem top(value: uint64) {
    ensures value <= 18446744073709551615u64 by {
        normalize();
    }
    ensures 0u64 <= value by {
        normalize();
    }
}
```

```expect
pass
```
