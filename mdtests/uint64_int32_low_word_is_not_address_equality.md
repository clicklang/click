# A low word does not establish equal byte addresses

Truncating the native index discards its high bits and can change its signed
interpretation. That equality cannot replace equality of exact observations.

```click
theorem low_word(bytes: uint8[], wide: uint64, index: int32) {
    requires wide as uint32 as int32 == index;
    ensures bytes + wide == bytes + index by {
        close() using { wide as uint32 as int32 == index; };
    }
}
```

```expect
fail: `close() using` could not prove the current goal from only its listed premises
```
