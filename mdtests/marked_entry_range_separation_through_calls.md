# A marked entry separation follows by-value fields through calls

The entry mark names the destination range before the parameter copy.
The pointer and size returned by the observers equal those incoming fields,
so `solve()` can cite the marked separation after rewriting both results.

```c filename=range.c
struct Slice {
    unsigned char *data;
    unsigned long size;
};

unsigned char *data(const struct Slice *slice) {
    return slice->data;
}

unsigned long length(const struct Slice *slice) {
    return slice->size;
}

unsigned long probe(struct Slice dst, const unsigned char *src, unsigned long n) {
    unsigned char *bytes = data(&dst);
    unsigned long size = length(&dst);
    return size;
}
```

```click
verifying "range.c";

uint8* data(const struct Slice* slice) {
    views slice->data;
    ensures result == slice->data;
}

uint64 length(const struct Slice* slice) {
    views slice->size;
    ensures result == slice->size;
}

uint64 probe(struct Slice dst, const uint8* src, uint64 n) {
    owns uninitialized(dst.data[0..dst.size]);
    views src[0..n];
    ensures result == old(dst.size);
} by {
    mark inputs;
    step_until(call(length, 0).entry);
    step();
    have separate(memory(at(call(data, 0).exit, call(data, 0).result)[0u64..call(length, 0).result]), memory(src[0..n])) by {
        solve();
    }
}
```

```expect
pass
```
