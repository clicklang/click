# The two weaker bounds of a defined float cast can be proved together

```click
theorem safe(x: double) {
    requires x > float64_from_bits(0);
    requires x < float64_from_bits(0x3ff0000000000000u64);
    ensures defined(x as int32);
}
```

```expect
pass
```
