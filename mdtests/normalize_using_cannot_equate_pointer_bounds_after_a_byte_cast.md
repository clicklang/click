# An offset equality cannot supply bounds after a widening pointer cast

The two pointers have the same address and provenance. The original parameter
has opaque bounds, and the conversion to a byte pointer forms the byte view of
the allocation (C11 6.3.2.3p7).

```c filename=cast.c
float* identity(float* p) { return p; }
```

```click
verifying "cast.c";

float* identity(float* p) {
    ensures result == (p as (uint8 *) as (float *));
} by {
    step();
    have result == (p as (uint8 *) as (float *)) by {
        close() using {};
    }
}
```

```expect
fail: `close() using` could not prove the current goal from only its listed premises
```
