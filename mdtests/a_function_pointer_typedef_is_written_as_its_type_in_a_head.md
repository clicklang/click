# A function-pointer typedef is written as its type in a head

A head writes a scalar, pointer or struct typedef name of the verified source,
but not a function-pointer alias; it writes that parameter's C declarator
instead.

```c filename=main.c
typedef int (*unary)(int);

int apply(unary f, int x) {
    return f(x);
}
```

```click
verifying "main.c";

int apply(unary f, int x) {
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: the typedef `unary` stands for an array, function pointer
```
