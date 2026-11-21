# A call accepts proved initialization of a symbolic byte range

The caller holds an initialized source through a pointer field and a
separate destination whose bytes may be unwritten. The call checks
initializedness for the exact source range it borrows.

```c filename=source.c
struct Input { const unsigned char* data; };

unsigned long inspect(const unsigned char* bytes, unsigned long n) {
    return n;
}

unsigned long probe(const struct Input* src, unsigned char* dst, unsigned long n, unsigned long m) {
    return inspect(src->data, n);
}
```

```click
verifying "source.c";

uint64 inspect(const uint8* bytes, uint64 n) {
    views bytes[0..n];
    ensures result == n;
}

uint64 probe(const struct Input* src, uint8* dst, uint64 n, uint64 m) {
    views src->data;
    views src->data[0..m];
    owns uninitialized(dst[0..n]);
    requires n > 0u64;
    requires n <= m;
    requires forall (k: uint64) { 0u64 <= k and k < m implies defined(src->data[k]) };
    ensures result == n;
} by {
    step() {
        requires forall (k: uint64) { 0u64 <= k and k < n implies defined(src->data[k]) } by {
            intro();
            intro();
            have k < m by { solve(); }
            instantiate(forall (i: uint64) { 0u64 <= i and i < m implies defined(src->data[i]) }, k);
            known();
        }
    }
}
```

```expect
pass
```
