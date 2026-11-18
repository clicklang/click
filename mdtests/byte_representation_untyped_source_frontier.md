# An untyped representation copy does not establish a typed value

The representation-copy rule transfers typed cells from the source. A raw byte
source has no typed cells, so a byte-exact copy of an opaque buffer leaves the
destination without a typed value and the `dst->x` load is refused. This is the
guard against reading arbitrary bytes as an invented typed value.
The copy's proof uses the fresh destination's separation from the source view.

```c filename=scalar_untyped_memcpy.c
void *malloc(unsigned long size);
void free(void *ptr);
void *memcpy(void *dest, const void *src, unsigned long n);
struct box { unsigned int x; };
int h(unsigned char *raw) {
    struct box *dst = malloc(sizeof(struct box));
    if (dst == 0) { return -1; }
    memcpy((unsigned char *)(void *)dst, raw, sizeof(struct box));
    int out = (int)dst->x;
    free(dst);
    return out;
}
```

```click
verifying "scalar_untyped_memcpy.c";

int h(uint8 raw[]) {
    views raw[0..4];
    ensures result == 0 or result == -1;
} by {
    step();
    step();
    branch {
        step();
        normalize();
    } else {
    }
    step() {
        requires separate(memory((dst as (uint8 *))[0..4]), memory(raw[0..4])) by { normalize(); }
    }
}
```

```expect
fail: read of uninitialized storage
```
