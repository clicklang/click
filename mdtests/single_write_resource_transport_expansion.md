# Single-statement preservation of an abstract resource field

```c filename=resource_frame.c
void keep(int *p) { *p = 7; }
```

```click
verifying "resource_frame.c";
abstract resource model() { field value: int32; }
void keep(int *p) {
    owns *p;
    owns m: model();
    requires separate(memory(*p), m);
} by {
    step();
    have separate(statement(0).footprint, m) by {
        normalize() using { separate(memory(*p), m); };
    }
    have m.value == at(statement(0).entry, m.value) by {
        preserve(separate(statement(0).footprint, m));
    }
    step();
}
```

```expect
pass
```
