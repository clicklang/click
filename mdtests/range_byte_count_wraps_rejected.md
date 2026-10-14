# range byte counts must not wrap at 32 bits

```c filename=t.c
int32 symn(int32 p[], int32 n) {
    return 0;
}
```

```click
verifying "t.c";

int32 symn(int32 p[], int32 n) {
    requires viewable(p[0..1]);
    requires n == 1073741825;
    ensures viewable(p[0..n]);
}
```

```expect
fail: kernel lowering produced no path: a memory range is too wide to be a 32-bit byte extent
```
