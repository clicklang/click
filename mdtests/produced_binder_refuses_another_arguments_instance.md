# A produced binder does not take an instance at other arguments

`move_out` produces `after: cell_at(c)`, but the only `cell_at` instance it
ends holding is the one `write` produced at `d`. The exit's produced binder
takes that instance by its family, and the clause, which reads its arguments,
refuses it.

```c filename=produced_binder_refuses_another_arguments_instance.c
struct cell { int value; };

void write(struct cell *c, int v) {
    c->value = v;
}

void move_out(struct cell *c, struct cell *d, int x) {
    write(d, x);
}
```

```click
verifying "produced_binder_refuses_another_arguments_instance.c";

resource cell_at(c: struct cell*) {
    field value: int32;
    owns c->value;
    fact c->value == value;
}

void write(struct cell* c, int32 v) {
    consumes before: cell_at(c);
    produces after: cell_at(c);
    ensures after.value == v;
} by {
    let {} = unfold(before);
    execute();
    let after = fold(cell_at(c), { value: v }, {});
}

void move_out(struct cell* c, struct cell* d, int32 x) {
    consumes before: cell_at(d);
    produces after: cell_at(c);
} by {
    execute();
    simp();
}
```

```expect
fail: Requires produces after: cell_at(c)
```
