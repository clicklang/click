# First byte of a nonempty native suffix

```c filename=suffix.c
unsigned char first(const unsigned char *p, unsigned long whole, unsigned long remaining) {
    const unsigned char *q = p + (whole - remaining);
    return *q;
}
```

```click
target "x86_64-linux-userspace";
verifying "suffix.c";
uint8 first(const uint8* p, uint64 whole, uint64 remaining) {
    requires whole <= 5551u64;
    requires remaining <= whole;
    views p[0u64..whole];
    ensures result == result;
} by { execute(); simp(); }
```

```expect
fail: missing resource fact
```
