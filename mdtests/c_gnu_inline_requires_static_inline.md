# `gnu_inline` is accepted only on `static inline`

On a non-static function `gnu_inline` changes which definition is emitted, which is not modeled.

```c filename=c_gnu_inline_requires_static_inline.c
int helper(int value) __attribute__((gnu_inline));

int32 run(int32 value) {
    return value;
}
```

```click
verifying "c_gnu_inline_requires_static_inline.c";

int32 run(int32 value) {
    ensures result == value by auto;
}
```

```expect
fail:c_gnu_inline_requires_static_inline.c:1: the GNU gnu-inline attribute requires `static inline` or `static __always_inline`
```
