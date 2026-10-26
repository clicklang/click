# Stepping past a branch arm names its shared-continuation limit

The `branch` arm reaches its boundary, the shared continuation after the C
`if`, before function exit. A `step()` past that boundary is refused, and the
refusal must name the branch-arm rule instead of claiming that the function
has no exit path.

```c filename=f.c
void mark_one(int32 a[], int32 n, int32 i, int32 m, int32 c) {
    if (c) {
        a[i] = 1;
    }
}
```

```click
verifying "f.c";

void mark_one(int32 a[], int32 n, int32 i, int32 m, int32 c) {
    requires 0 <= i;
    requires i < n;
    requires 0 <= m;
    requires m < n;
    requires m != i;
    requires n <= 1073741823;
    owns a[0..n];
    ensures a[m] == old(a[m]);
} by {
    mark entry;
    branch {
        step();
        step();
    } else {}
}
```

```expect
fail: `step()` ran past the end of its branch body; an arm of `branch` must stop at the shared continuation
```
