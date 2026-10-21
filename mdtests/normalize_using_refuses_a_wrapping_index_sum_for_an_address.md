# `normalize using` refuses a wrapping index sum for an address

A native `uint64` sum wraps. The premise
`to_integer(total) == to_integer(prefix + suffix)` is the native comparison
`total == prefix + suffix`, so it does not make `bytes + total` the address
`(bytes + prefix) + suffix`: the cited premise must state the exact Integer sum.

```click
theorem native_offset_sum(bytes: uint8[], prefix: uint64, suffix: uint64, total: uint64) {
    requires to_integer(total) == to_integer(prefix + suffix);
    ensures (bytes + prefix) + suffix == bytes + total by {
        normalize() using { to_integer(total) == to_integer(prefix + suffix); };
    }
}
```

```expect
fail: goal did not normalize to true using the listed conditions
```
