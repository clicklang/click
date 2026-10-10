# Truncating a large complete prefix does not preserve divisibility

The divisor three does not divide 2^32. A full-width prefix cannot be
narrowed into a signed word without its bound.

```click
theorem complete_prefix(n: uint64) {
    ensures (((int32)(uint32)(n - n % 3u64)) % 3) == 0 by normalize();
}
```

```expect
fail: normalize
```
