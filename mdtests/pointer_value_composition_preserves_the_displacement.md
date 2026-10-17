# Pointer composition preserves the displacement

```c filename=compose.c
void compose(const unsigned char *base, const unsigned char *middle, const unsigned char *end) {}
```

```click
verifying "compose.c";
void compose(const uint8* base, const uint8* middle, const uint8* end) {
 requires middle == base + 2u64;
 requires end == middle + 3u64;
 ensures end == base + 6u64;
} by {
 execute();
 simp() using { end == middle + 3u64; middle == base + 2u64; };
}
```

```expect
fail: checked outcome `simp() using` search did not retain a complete proof
```
