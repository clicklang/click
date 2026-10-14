# repeated calls retain distinct model-field values

The two increments update one resource's model field. The second checked
postcondition relates its new value to the first call's value. A trace must
keep those identities distinct even when both have the source hint `c.value`.

```c filename=field-history.c
struct cell { int32 value; };
void twice(struct cell* p) {
    increment(p);
    increment(p);
}
```

```click
verifying "field-history.c";
resource counter(p: struct cell*) {
    field value: int32;
    owns p->value;
    fact p->value == value;
}
extern void increment(struct cell* p) {
    owns c: counter(p);
    requires c.value <= 2147483646;
    ensures c.value == old(c.value) + 1;
}
void twice(struct cell* p) {
    owns c: counter(p);
    requires c.value == 0;
    ensures c.value == 2;
} by {
    step(increment(p), { c: c });
    have c.value == 1 by { simp(); }
    have c.value <= 2147483646 by { rewrite(c.value == 1); normalize(); }
    step(increment(p), { c: c });
    step();
    simp();
}
```

```expect
pass
```
