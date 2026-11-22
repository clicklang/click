# Pointer subtraction widens the model's narrow coordinates

The difference of two signed 32-bit coordinates always fits `ptrdiff_t` on
this target. The function's result retains that width.

```c filename=c_pointer_distance_widens_coordinates.c
long distance(int32 *left, int32 *right) {
    return right - left;
}
```

```click
verifying "c_pointer_distance_widens_coordinates.c";

int64 distance(int32* left, int32* right) {
    requires same_allocation(left, right);
    ensures result == right - left;
}
```

```expect
pass
```
