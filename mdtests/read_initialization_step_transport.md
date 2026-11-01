# Explicit read initialization across one separated store

```c filename=initialization.c
void change(int *p, int *q) {
    *q = 1;
}
```

```click
verifying "initialization.c";
void change(int32* p, int32* q) {
    owns uninitialized(p[0..1]);
    owns *q;
    requires defined(*p);
    requires separate(memory(*p), memory(*q));
    ensures defined(*p);
} by {
    mark before;
    step();
    have separate(statement(0).footprint, memory(*p)) by {
        normalize() using { separate(memory(*p), memory(*q)); };
    }
    have defined(*p) by {
        transport(at(before, defined(*p)), defined(*p)) using {
            at(before, defined(*p));
            separate(statement(0).footprint, memory(*p));
        };
    }
    step();
}
```

```expect
pass
```
