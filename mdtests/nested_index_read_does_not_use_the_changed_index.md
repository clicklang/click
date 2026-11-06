# A saved nested read does not use a later index

The returned value is `a[1]`, not the `a[0]` selected after changing `*p`.

```c filename=nested_index.c
int lookup_then_change(int *a, int *p) {
    int value = a[*p];
    *p = 0;
    return value;
}
```

```click
verifying "nested_index.c";
int32 lookup_then_change(int32* a, int32* p) {
    views a[0..4];
    owns *p;
    requires *p == 1;
    requires a[0] == 10;
    requires a[1] == 20;
    requires separate(memory(*p), memory(a[0..4]));
    ensures result == a[*p];
}
```

```expect
fail: `ensures result == a[*p]` failed
```
