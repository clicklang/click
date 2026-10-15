# Printed float-cast bounds can be reused as contract prerequisites

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
    requires d < 2147483648i64;
    ensures result >= 0;
} by {
    branch then { step(); simp(); } else {}
    step();
    simp();
}
```

```expect
pass
```
