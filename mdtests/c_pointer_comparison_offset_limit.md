# Click identifies unsupported offsets in ordered pointer comparison

```c filename=c_pointer_comparison_offset_limit.c
int within_input(const unsigned char *p, size_t offset, size_t length) {
    const unsigned char *end = (p + offset) + 1;
    return end > p;
}
```

```click
verifying "c_pointer_comparison_offset_limit.c";

int32 within_input(const uint8* p, uint64 offset, uint64 length) {
    views p[0..length];
    requires p != 0;
    requires offset < length;
    requires length <= 2147483647u64;
    ensures result == 1;
}
```

```expect
fail: Click does not yet support ordered pointer comparison with these offsets
```
