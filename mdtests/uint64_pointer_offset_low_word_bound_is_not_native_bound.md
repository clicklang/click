# A low-word bound does not fix the native pointer displacement

The index can be 2^32 even when its signed low word is zero.

```click
theorem refused(pointer: int32*, index: uint64) {
    requires 0 <= index as int32;
    requires index as int32 <= 1073741823;
    ensures pointer + index as int32 == pointer + index by {
        solve() using { 0 <= index as int32; index as int32 <= 1073741823; };
    }
}
```

```expect
fail: could not prove the current goal
```
