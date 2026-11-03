# a sidecar cannot declare an axiom

```click
axiom zero_is_one(x: uint32) {
    ensures x == 0u32;
}
```

```expect
fail: an `axiom` is reserved for the Click library
```
