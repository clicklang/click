# A const table stays read-only behind a const-dropping cast

```c filename=c_const_cast_table_write_rejected.c
const int table[2] = {1, 2};

int32 run(void) {
    int *p = (int *)table;
    p[0] = 3;
    return table[0];
}
```

```click
verifying "c_const_cast_table_write_rejected.c";

int32 run() {
    ensures result == result by auto;
}
```

```expect
fail: invalid memory access
```
