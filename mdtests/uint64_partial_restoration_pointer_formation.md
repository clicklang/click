# Advancing a remaining-count cursor stays within its original range

The original cursor subtracts the remaining count, then advances by at most
that count. Its original view supplies the bounds for both pointer additions.

```c filename=chunk.c
int32 chunk_step(uint8 *bytes, uint64 bytes_len, uint64 remaining, uint64 size) {
    uint8 *cursor = bytes + (bytes_len - remaining);
    if (size <= remaining) {
        uint8 *next = cursor + size;
    }
    return 0;
}
```

```click
verifying "chunk.c";
int32 chunk_step(uint8 *bytes, uint64 bytes_len, uint64 remaining, uint64 size) {
    views bytes[0u64..bytes_len];
    requires bytes_len <= 2147483647u64;
    requires remaining <= bytes_len;
    ensures result == 0;
} by { execute(); }
```

```expect
pass
```
