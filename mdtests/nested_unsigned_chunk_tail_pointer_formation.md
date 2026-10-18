# Nested unsigned chunk tails stay within the original slice

The captured pointer keeps its original view. Both unsigned subtractions
remove remainders without wrapping; their resulting position is at most
the original full-width length.

```c filename=chunk.c
int32 chunk_tail(uint8 *bytes, uint64 bytes_len, uint64 chunk_size) {
    uint64 tail_len = bytes_len % 4u;
    uint64 complete = bytes_len - tail_len;
    uint8 *captured = bytes;
    uint64 nested_tail = complete % chunk_size;
    uint64 remaining = complete - nested_tail;
    uint8 *tail = captured + remaining;
    return 0;
}
```

```click
verifying "chunk.c";
int32 chunk_tail(uint8 *bytes, uint64 bytes_len, uint64 chunk_size) {
    views bytes[0u64..bytes_len];
    requires bytes_len <= 2147483647u64;
    requires 0u64 < chunk_size;
    ensures result == 0;
} by { execute(); }
```

```expect
pass
```
