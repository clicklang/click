# A saved descriptor cannot observe a named instance after it opens

```c filename=observe_open.c
int read_cell(int *p) { return *p; }
```

```click
verifying "observe_open.c";

resource cell(p: int32*) {
    field tag: int32;
    owns *p;
}

int32 read_cell(int32* p) {
    owns c: cell(p);
} by {
    mark saved;
    unfold(c);
    observe(at(saved, c));
    step_until(function.exit);
}
```

```expect
fail: instance is not exclusively owned in folded form
```
