# A callee cannot write const storage through a cast either

```c filename=c_const_cast_callee_write_rejected.c
static void overwrite(const int *q) {
    int *p = (int *)q;
    *p = 7;
}

const int limit = 3;

int32 run(void) {
    overwrite(&limit);
    return limit;
}
```

```click
verifying "c_const_cast_callee_write_rejected.c";

int32 run() {
    ensures result == result by auto;
}
```

```expect
fail: invalid memory access
```
