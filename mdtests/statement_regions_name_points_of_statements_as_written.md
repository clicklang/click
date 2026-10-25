# Statement regions name points of the statements as written

`statement(i)` is the region of the `i`th statement of the function body as
written, counting from zero: each block item, declarations included. Its
`.entry` is before the first atomic region `step()` crosses for it, and its
`.exit` is after the last. A statement's calls are atomic regions of their
own, so `y = f(f(y));` is two: the inner call, then the outer call assigned to
`y`. `statement(1).call(f, 1)` is the outer call, since calls are counted in
the order they run, and `statement(1).region(1)` is the same atomic region by
its index.

```c filename=statement_paths.c
int32 f(int32 v) { return v + 1; }
int32 probe(int32 x) {
    int32 y = f(x);
    y = f(f(y));
    return y;
}
```

```click
verifying "statement_paths.c";

int32 f(int32 v) {
    requires v < 1000;
    ensures result == v + 1;
}

int32 probe(int32 x) {
    requires x < 10;
    ensures result == x + 3;
} by {
    step(); step(); step(); step(); step();
    have at(statement(0).exit, y) == x + 1 by simp();
    have at(statement(1).entry, y) == x + 1 by simp();
    have at(statement(1).call(f, 1).entry, y) == x + 1 by simp();
    have at(statement(1).region(1).entry, y) == x + 1 by simp();
    have at(statement(1).exit, y) == x + 3 by simp();
    simp();
}
```

```expect
pass
```
