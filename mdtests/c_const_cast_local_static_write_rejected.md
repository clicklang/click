# A function-local static const object stays read-only behind a cast

```c filename=c_const_cast_local_static_write_rejected.c
int32 run(void) {
    static const int local = 5;
    int *p = (int *)&local;
    *p = 6;
    return local;
}
```

```click
verifying "c_const_cast_local_static_write_rejected.c";

int32 run() {
    ensures result == result by auto;
}
```

```expect
fail: invalid memory access
```
