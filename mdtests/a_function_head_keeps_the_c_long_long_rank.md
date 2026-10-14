# A function head keeps the C `long long` rank

A function head restates the C declaration, so it has the declaration's exact
C types. `long` and `long long` are distinct C types with the same
representation; a head for a `long long` function writes `long long`.

```c filename=main.c
long long first(long long *p) {
    return p[0];
}

unsigned long long *same(unsigned long long *p) {
    return p;
}
```

```click
verifying "main.c";

long long first(long long *p) {
    views p[0];
    ensures result == p[0];
} by {
    execute();
    simp();
}

unsigned long long *same(unsigned long long *p) {
    ensures result == p by auto;
}
```

```expect
pass
```
