# A function head's `int64` does not restate a C `long long`

`int64` is `long` in a function head, as in Click's C dialect, so it does not
restate a `long long` declaration. The mismatch names both C types.

```c filename=main.c
long long first(long long *p) {
    return p[0];
}
```

```click
verifying "main.c";

int64 first(long long *p) {
    views p[0];
    ensures result == p[0];
}
```

```expect
fail: .click return type is `long`, C return type is `long long`
```
