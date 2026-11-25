# A selected shift by a variable still requires a count bound

```click
theorem unknown_count(flag: Bool, z: uint64, w: uint64) {
    requires flag;
    ensures (if flag { z >> w } else { z }) == z by {
        close() using { flag; };
    }
}
```

```expect
fail: it denotes a value only where
```
