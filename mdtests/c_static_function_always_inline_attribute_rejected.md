# The always-inline attribute still requires `static inline`

Accepting `static` functions does not widen where the inline-only attributes
may appear.

```c filename=c_static_function_always_inline_attribute_rejected.c
static __attribute__((always_inline)) int add_one(int value) {
    return value + 1;
}

int32 run(int32 value) {
    return value;
}
```

```click
verifying "c_static_function_always_inline_attribute_rejected.c";

int32 run(int32 value) {
    ensures result == value by auto;
}
```

```expect
fail:c_static_function_always_inline_attribute_rejected.c:1: the GNU always-inline attribute requires `static inline` or `static __always_inline`
```
