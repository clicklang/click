# A release footprint includes the allocation's memory

The allocation token alone is not the effect of `free`. The footprint must
prevent preservation of a cell inside the released allocation.

```c filename=release.c
void dispose(int32 *data, int32 n) { free(data); }
```

```click
verifying "release.c";
resource cell(p: int32*, n: int32) {
    owns allocation(p, n * 4);
    owns p[0..n];
}
void dispose(int32 *data, int32 n) {
    requires 0 < n;
    requires n < 100;
    consumes cell(data, n);
} by {
    unfold(cell(data, n));
    step();
    have separate(statement(0).footprint, memory(data[0..n])) by {
        normalize() using {};
    }
}
```

```expect
fail: goal did not normalize to true
```
