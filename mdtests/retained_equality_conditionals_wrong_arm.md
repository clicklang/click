# A selected invalid shift remains undefined with a wide equality guard

```click
theorem selected_invalid_equality_shift() {
    ensures (if 9u64 == 9u64 { 1u64 << 64u64 } else { 3u64 }) == 3u64 by { normalize(); }
}
```

```expect
fail: it denotes a value only where
```
