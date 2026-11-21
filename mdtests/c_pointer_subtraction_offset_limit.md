# Click identifies unsupported offsets in pointer subtraction

```c filename=c_pointer_subtraction_offset_limit.c
int within_input(const unsigned char *p, size_t offset, size_t length) {
    const unsigned char *end = (p + offset) + 1;
    return (size_t)(end - p) < length;
}
```

```click
verifying "c_pointer_subtraction_offset_limit.c";

int32 within_input(const uint8* p, uint64 offset, uint64 length) {
    views p[0..length];
    requires p != 0;
    requires offset < length;
    requires length <= 2147483647u64;
    ensures (offset + 1u64) < length implies result == 1;
    ensures length <= (offset + 1u64) implies result == 0;
}
```

```expect
fail: tactic failure: `step()` failed while executing C: Click does not yet support pointer subtraction with these offsets
```
