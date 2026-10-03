# A const aggregate stays read-only behind a const-dropping cast

```c filename=c_const_cast_aggregate_write_rejected.c
struct pair {
    int first;
    int second;
};

const struct pair fixed = {1, 2};

int32 run(void) {
    struct pair *p = (struct pair *)&fixed;
    p->first = 3;
    return fixed.first;
}
```

```click
verifying "c_const_cast_aggregate_write_rejected.c";

int32 run() {
    ensures result == result by auto;
}
```

```expect
fail: invalid memory access
```
