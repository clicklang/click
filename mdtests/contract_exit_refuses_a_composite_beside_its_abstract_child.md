# A contract exit cannot return a composite and the abstract child it contains

`boxed(a)` contains the abstract `ticket(a->id)`. With `a->id == 1`,
returning `boxed(a)` and `ticket(1)` would duplicate the contained ticket.
An abstract ticket cannot be folded from nothing, so the closer finds no
second one.

```c filename=abstract_child.c
struct box { int32 id; };
int32 f(struct box* a) {
    return 0;
}
```

```click
abstract resource ticket(id: int32);
resource boxed(a: struct box*) {
    owns a->id;
    owns ticket(a->id);
}
verifying "abstract_child.c";
int32 f(struct box* a) {
    requires a != 0;
    requires a->id == 1;
    owns boxed(a);
    produces ticket(1);
}
```

```expect
fail: missing resource fact
```
