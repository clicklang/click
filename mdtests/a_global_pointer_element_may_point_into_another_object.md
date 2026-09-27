# a global pointer element may point into another object

A function's entry names every element of a global array it knows nothing
about as one run of cells, whatever the array's length. An element of pointer
type holds a fresh symbolic pointer, which may point into any block: here
into `g`, so the comparison has a path on which it holds. Spelled the way a
seeded range spells a pointer, as a pointer into the run's own block, the
element would be proven distinct from `&g[0]` and `result == 0` would
verify.

```c filename=a_global_pointer_element_may_point_into_another_object.c
int32 g[1];
int32 *ptrs[100];

int32 points_elsewhere() {
    return ptrs[7] == &g[0];
}
```

```click
verifying "a_global_pointer_element_may_point_into_another_object.c";

int32 points_elsewhere() {
    ensures result == 0;
} by { execute(); simp(); }
```

```expect
fail: left side evaluated to 1, right side evaluated to 0
```
