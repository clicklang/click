# An unconstrained pointer's address is not zero

```click
theorem unknown_address(p: int32*, x: uint64) {
    ensures address(p) + x == x by { close(); }
}
```

```expect
fail: could not establish `(address(p) + x) == x`
```
