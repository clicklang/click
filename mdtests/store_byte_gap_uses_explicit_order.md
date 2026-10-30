# Explicit endpoint order replaces automatic byte-gap walks

The wide store uses one stated endpoint order instead of walking an ambient
order chain. The proof establishes that endpoint order with an expandable solve.

```c filename=store_geometry.c
int32 wide_after(int32* a, int32 i, int32 middle, int32 j) {
    int64* w;
    a[i] = 5;
    w = (int64*)(void*)&a[j];
    *w = 0;
    return a[i];
}
```

```click
verifying "store_geometry.c";

int32 wide_after(int32* a, int32 i, int32 middle, int32 j) {
    requires 0 <= i;
    requires i < middle;
    requires middle < j;
    requires j < 3;
    owns a[0..4];
    ensures result == 5;
} by {
    have i < j by solve() using { i < middle; middle < j; };
    step_until(function.exit);
}
```

```expect
pass
```
