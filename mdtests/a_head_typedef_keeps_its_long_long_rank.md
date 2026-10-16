# A typedef in a head keeps its `long long` rank

A typedef name in a function head stands for exactly its type. An alias of
`long long` is not `long`, so it does not restate a `long` declaration.

```c filename=main.c
typedef long long wide;

long first(long *p) {
    return p[0];
}
```

```click
verifying "main.c";

wide first(long *p) {
    views p[0];
    ensures result == p[0];
} by {
    execute();
    simp();
}
```

```expect
fail: .click return type is `long long`, C return type is `long`
```
