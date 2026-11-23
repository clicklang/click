# XOR can cancel its literal operand

```click quick-solve
theorem xor_can_cancel(d: uint32) {
    ensures (d ^ 1u32) != 0u32 by {
        solve();
    }
}
```

```expect
fail: could not establish
```
