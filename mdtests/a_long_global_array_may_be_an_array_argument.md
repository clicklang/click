# a long global array may be the array argument

A function's entry names every element of a global array it knows nothing
about as one run of cells, whatever the array's length. That changes nothing
about what the array may alias: a caller may pass `buf + 500` as `a`, so a
store into `buf[500]` may write `a[0]`, and `a[0] == 5` is not carried across
it. The long-array twin of `global_may_alias_an_array_argument.md`.

```c filename=a_long_global_array_may_be_an_array_argument.c
int32 buf[1000];

void f(int32 a[], int32 n) {
    buf[500] = 1;
}
```

```click
verifying "a_long_global_array_may_be_an_array_argument.c";

void f(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires a[0] == 5;
    owns buf[500..501];
    ensures a[0] == 5;
} by { execute(); simp(); }
```

```expect
fail: `a[0]` may have changed since earlier in this function
```
