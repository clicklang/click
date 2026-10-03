# An `error` function may only be called as a discarded statement

Only the `compiletime_assert` shape is modeled: a discarded call with no arguments.

```c filename=c_error_function_value_call_rejected.c
int32 run(int32 value) {
    __attribute__((__noreturn__)) extern int fail(void) __attribute__((__error__("no")));
    return fail();
}
```

```click
verifying "c_error_function_value_call_rejected.c";

```

```expect
fail:c_error_function_value_call_rejected.c:3: function `fail` is declared with the GNU `error` attribute; only a discarded call with no arguments is supported
```
