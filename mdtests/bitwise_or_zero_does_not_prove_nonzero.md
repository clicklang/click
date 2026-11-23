# OR with zero cannot establish a nonzero divisor

```click quick-solve
theorem no_set_bit(d: uint32) {
    ensures (d | 0u32) != 0u32 by {
        solve();
    }
}
```

```expect
fail: could not establish
```
