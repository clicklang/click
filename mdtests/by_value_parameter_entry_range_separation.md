# A by-value parameter names its input range in a separation proof

The contract separates the destination bytes from the source view. A mark at
the start of the proof records the incoming parameter's pointer and length,
before the first step binds the body's private parameter. The marked fields
name the range from the contract, so the proof can cite the separation with
`known()`.

```c filename=range.c
struct Slice {
    unsigned char *data;
    unsigned long size;
};

unsigned long probe(struct Slice dst, const unsigned char *src, unsigned long n) {
    unsigned long size = dst.size;
    return size;
}
```

```click
verifying "range.c";
uint64 probe(struct Slice dst, const uint8* src, uint64 n) {
    owns uninitialized(dst.data[0..dst.size]);
    views src[0..n];
    ensures result == old(dst.size);
} by {
    mark inputs;
    step();
    have separate(memory(at(inputs, dst.data)[0u64..at(inputs, dst.size)]), memory(src[0..n])) by {
        known();
    }
    step();
}
```

```expect
pass
```
