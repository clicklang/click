# Pointer composition cannot gain identity from an address

```c filename=compose.c
void compose(const unsigned char *base, const unsigned char *middle, const unsigned char *end) {}
```

```click
verifying "compose.c";
void compose(const uint8* base, const uint8* middle, const uint8* end) {
 requires address(middle) == address(base + 2u64);
 requires end == middle + 3u64;
 ensures end == base + 5u64;
} by {
 execute();
 simp() using { end == middle + 3u64; address(middle) == address(base + 2u64); };
}
```

```expect
fail: checked outcome `simp() using` search did not retain a complete proof
```
