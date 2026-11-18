# An offset equality cannot supply bounds after a widening pointer cast

The two pointers have the same address and provenance. The original parameter
has opaque bounds, and the cast through `void *` selects the enclosing object.

```c filename=cast.c
float* identity(float* p) { return p; }
```

```click
verifying "cast.c";

float* identity(float* p) {
    ensures result == (p as (void *) as (float *));
} by {
    step();
    have result == (p as (void *) as (float *)) by {
        normalize() using {};
    }
}
```

```expect
fail: goal did not normalize to true using the listed conditions
```
