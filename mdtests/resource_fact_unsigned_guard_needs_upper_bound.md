# An unsigned binder's guard must still bound it below the range end

The type of a `uint64` binder supplies its lower bound, not its upper one.
`k <= len` admits `k == len`, one past the contained `views bytes[0u64..len]`,
so the fact's read of `bytes[k]` is refused.

```c filename=probe.c
uint8 first(uint8 bytes[], uint64 len) { return bytes[0]; }
```

```click
verifying "probe.c";
resource prefix(bytes: uint8*, len: uint64) {
    views bytes[0u64..len];
    fact forall (k: uint64) { k <= len implies bytes[k] != '\0' };
}
uint8 first(uint8 bytes[], uint64 len) {
    requires 0u64 < len;
    views prefix(bytes, len);
    ensures true;
} by { execute(); simp(); }
```

```expect
fail: without a covering contained memory resource
```
