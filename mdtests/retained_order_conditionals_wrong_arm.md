# A retained order guard does not discharge its selected arm's domain

```click
theorem wrong_arm() {
    ensures (if 9u64 < 10u64 { 1u64 << 64u64 } else { 3u64 }) == 3u64 by {
        close();
    }
}
```

```expect
fail: it denotes a value only where
```
