# Reading the first element of an array parameter views one cell

This checks that an `int32 p[]` parameter read at `p[0]` verifies with a
one-cell `views p[0..1]` clause that supplies the read's viewability.

```c filename=array_parameter_first_element_views_one_cell.c
int32 first(int32 p[]) {
    return p[0];
}
```

```click
verifying "array_parameter_first_element_views_one_cell.c";

int32 first(int32 p[]) {
    views p[0..1];
    ensures result == p[0] by auto();
}
```

```expect
pass
```
