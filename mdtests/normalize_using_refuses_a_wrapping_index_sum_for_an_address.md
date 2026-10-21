# `normalize using` refuses a wrapping index sum for an address

A native `uint64` sum wraps, so `total == prefix + suffix` does not make
`bytes + total` the address `(bytes + prefix) + suffix`: the cited premise must
state the exact Integer sum.

```click
theorem native_offset_sum(bytes: uint8[], prefix: uint64, suffix: uint64, total: uint64) {
    requires total == prefix + suffix;
    ensures (bytes + prefix) + suffix == bytes + total by {
        normalize() using { total == prefix + suffix; };
    }
}
```

```expect
fail: goal did not normalize to true using the listed conditions
```
