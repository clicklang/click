# Float-cast branch prerequisites retain source names and decimal bounds

```c filename=branch_float_cast.c
int32 positive(double d) {
    if ((int32) d > 0) {
        return 1;
    }
    return 0;
}
```

```click
verifying "branch_float_cast.c";

int32 positive(double d) {
    requires isfinite(d);
    requires d >= -2147483648;
    ensures result >= 0;
} by {
    branch { step(); simp(); } else {}
    step();
    simp();
}
```

```expect
fail: `d < 2147483648i64`
```
