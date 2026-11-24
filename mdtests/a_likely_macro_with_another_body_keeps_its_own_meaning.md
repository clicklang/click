# A `likely` macro with another body keeps its own meaning

A macro named `likely` that calls `__builtin_expect` on a different
expression is expanded as written. This one negates its condition, so for
`a == 1` the function returns `20`, not `10`.

```c filename=main.c
#define likely(x) __builtin_expect(!(x), 1)

int32 pick(int32 a) {
    if (likely(a == 1)) return 10;
    return 20;
}
```

```click
verifying "main.c";

int32 pick(int32 a) {
    requires a == 1;
    ensures result == 10;
}
```

```expect
fail: unclosed goal
```
