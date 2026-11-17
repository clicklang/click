# A call footprint contains every mutable argument resource

```c filename=call.c
void change_both(int *p, int *q) { *p = 1; *q = 2; }
void beside_call(int *p, int *q, int *r) { change_both(p, q); }
```

```click
verifying "call.c";
void change_both(int *p, int *q) { owns *p; owns *q; } by { step(); step(); step(); known(); known(); known(); known(); known(); }
void beside_call(int *p, int *q, int *r) {
    owns *p;
    owns *q;
    views *r;
    requires separate(memory(*p), memory(*r));
    requires separate(memory(*q), memory(*r));
    ensures *r == old(*r);
} by {
    step();
    have separate(statement(0).footprint, memory(*r)) by {
        normalize() using {
            separate(memory(*p), memory(*r));
            separate(memory(*q), memory(*r));
        };
    }
    have *r == at(statement(0).entry, *r) by {
        preserve(memory(*r), statement(0));
    }
    step();
    known(); known(); known();
    known(); known(); known();
}
```

```expect
pass
```
