# An array typedef is written as its type in a head

A head writes a scalar, pointer, struct or function-pointer typedef name of
the verified source, but not an array alias; it writes the parameter's C
type instead.

```c filename=main.c
typedef int triple[3];

int first(triple values) {
    return values[0];
}
```

```click
verifying "main.c";

int first(triple values) {
    views values[0];
    ensures result == values[0];
} by {
    execute();
    simp();
}
```

```expect
fail: the typedef `triple` stands for an array
```
