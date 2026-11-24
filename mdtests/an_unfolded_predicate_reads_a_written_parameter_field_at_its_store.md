# An unfolded predicate reads a written parameter field at its store

`reset` writes both fields of its struct parameter, then ensures a field
value and a predicate over both fields. The predicate argument names the
exit memory. Unfolding the predicate must read each field at the store that
wrote it, as `have` does at the same point, so `known` closes the predicate
goal from the proved body. The argument once dropped the point's recorded
path, and the unfolded body read the fields under a different identity.

```c filename=counter.c
struct counter { int32 used; int32 limit; };
void reset(struct counter* c, int32 limit) { c->used = 0; c->limit = limit; }
```

```click
import click::integer;

authorized resource slot(c: struct counter*) {}
resource storage(c: struct counter*) {
    owns *c;
    owns authority(slot(c));
}
predicate valid(c: struct counter*) {
    c->limit == c->used + count(slot(c))
}
verifying "counter.c";
void reset(struct counter* c, int32 limit) {
    consumes storage(c);
    requires 0 <= limit;
    requires count(slot(c)) == 0;
    ensures c->used == 0;
    ensures valid(c);
} by {
    unfold(storage(c));
    step();
    step();
    fold(limit of slot(c));
    step();
    unfold(valid(c));
    have to_integer(c->limit) == to_integer(c->used) + to_integer(count(slot(c))) by {
        close();
    }
    close();
    close();
}
```

```expect
pass
```
