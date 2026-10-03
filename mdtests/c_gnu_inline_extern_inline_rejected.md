# `extern inline` with `gnu_inline` stays rejected

This is the form whose meaning `gnu_inline` changes; it is not modeled.

```c filename=c_gnu_inline_extern_inline_rejected.c
extern inline __attribute__((gnu_inline)) int helper(int value) { return value; }

int32 run(int32 value) {
    return value;
}
```

```click
verifying "c_gnu_inline_extern_inline_rejected.c";

int32 run(int32 value) {
    ensures result == value by auto;
}
```

```expect
fail:c_gnu_inline_extern_inline_rejected.c:1: inline function definitions require `static inline` or `static __always_inline` in this slice
```
