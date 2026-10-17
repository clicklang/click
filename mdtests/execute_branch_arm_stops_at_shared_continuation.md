# `execute()` names a branch arm's shared-continuation limit

The arm reaches its boundary before function exit. Its refusal must name
the branch-arm rule instead of claiming that the function has no exit path.

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
        execute();
    } else {
        execute();
    }
    simp();
}
```

```expect
fail: an arm of `branch` must stop at the shared continuation
```
