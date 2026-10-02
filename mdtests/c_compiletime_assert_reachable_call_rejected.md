# A reachable call to an `error` function fails the proof

Nothing rules out the path that calls the function, so the unreachability check fails.

```c filename=c_compiletime_assert_reachable_call_rejected.c
int32 guarded(int32 value) {
    __attribute__((__noreturn__)) extern void __compiletime_assert_1(void) __attribute__((__error__("Unsupported access size.")));
    if (value)
        __compiletime_assert_1();
    return value;
}
```

```click
verifying "c_compiletime_assert_reachable_call_rejected.c";

int32 guarded(int32 value) {
    ensures result == value by auto;
}
```

```expect
fail: call to `__compiletime_assert_1`, declared with the GNU `error` attribute, is unreachable
```
