# A low word does not establish equal byte addresses

Truncating the native index discards its high bits and can change its signed
interpretation. That equality cannot replace equality of exact observations.

```click
theorem low_word(bytes: uint8[], wide: uint64, index: int32) {
    requires (int32)(uint32)wide == index;
    ensures bytes + wide == bytes + index by {
        normalize() using { (int32)(uint32)wide == index; }
    }
}
```

```expect
fail: normalize using
```
