# A low-word bound does not fix the native pointer displacement

The index can be 2^32 even when its signed low word is zero.

```click
theorem refused(pointer: int32*, index: uint64) {
    requires 0 <= (int32)index;
    requires (int32)index <= 1073741823;
    ensures pointer + (int32)index == pointer + index by {
        simp() using { 0 <= (int32)index; (int32)index <= 1073741823; }
    }
}
```

```expect
fail: could not prove the current goal
```
