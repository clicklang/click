# `__builtin_constant_p` is not assumed to be 0

The arm taken when the builtin yields 1 is checked too.

```c filename=c_builtin_constant_p_is_not_zero.c
int32 flag(int32 value) {
    if (__builtin_constant_p(value))
        return 1;
    return 0;
}
```

```click
verifying "c_builtin_constant_p_is_not_zero.c";

int32 flag(int32 value) {
    ensures result == 0 by auto;
}
```

```expect
fail: left side evaluated to 1, right side evaluated to 0
```
