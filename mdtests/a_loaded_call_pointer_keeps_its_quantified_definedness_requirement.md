# A loaded call pointer keeps its quantified definedness requirement

The caller can prove the bytes readable through a pointer loaded from a
field. Written in the caller, the clause also checks that the pointer field
is readable. The checked source form keeps that extra check.

```c filename=source.c
struct Input { const unsigned char* data; };

unsigned long inspect(const unsigned char* bytes, unsigned long n) {
    return n;
}

unsigned long probe(const struct Input* src, unsigned char* dst, unsigned long n) {
    return inspect(src->data, n);
}
```

```click
verifying "source.c";

uint64 inspect(const uint8* bytes, uint64 n) {
    requires forall (k: uint64) { k < n implies defined(bytes[k]) };
    ensures result == n;
}

uint64 probe(const struct Input* src, uint8* dst, uint64 n) {
    views src->data;
    views src->data[0..n];
    owns uninitialized(dst[0..n]);
    requires n > 0u64;
    requires forall (k: uint64) { k < n implies defined(src->data[k]) };
    ensures result == n;
} by {
    step() by { close(); }
}
```

```expect
pass
```
