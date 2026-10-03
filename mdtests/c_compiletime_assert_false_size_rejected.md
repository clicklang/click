# A false size assertion fails the proof

An `int` is not one byte, so the call is reachable.

```c filename=c_compiletime_assert_false_size_rejected.c
int32 store(int *cell, int32 value) {
    __attribute__((__noreturn__)) extern void __compiletime_assert_1(void) __attribute__((__error__("Unsupported access size.")));
    if (!(sizeof(*cell) == sizeof(char)))
        __compiletime_assert_1();
    return value;
}
```

```click
verifying "c_compiletime_assert_false_size_rejected.c";

int32 store(int32* cell, int32 value) {
    ensures result == value by auto;
}
```

```expect
fail: call to `__compiletime_assert_1`, declared with the GNU `error` attribute, is unreachable
```
