# A function's produced binder takes the instance a call produced

`set_and_get` consumes a `cell_at(c)` and produces one. `execute()` runs both
calls: each binds the only `cell_at` instance the caller holds, and the last
call produces a new one. No proof step names that instance, so it is held
under no name; at the exit, the produced binder `after` takes it, as the only
`cell_at` instance there, and the clause checks its arguments.

```c filename=produced_binder_takes_the_call_result.c
struct cell { int value; };

void write(struct cell *c, int v) {
    c->value = v;
}

int read(struct cell *c) {
    return c->value;
}

int set_and_get(struct cell *c, int x) {
    write(c, x);
    return read(c);
}
```

```click
verifying "produced_binder_takes_the_call_result.c";

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

int32 read(struct cell* c) {
    consumes before: cell_at(c);
    produces after: cell_at(c);
    ensures result == old(before.value);
    ensures after.value == old(before.value);
} by {
    let {} = unfold(before);
    execute();
    let after = fold(cell_at(c), { value: old(before.value) }, {});
}

int32 set_and_get(struct cell* c, int32 x) {
    consumes before: cell_at(c);
    produces after: cell_at(c);
    ensures result == x;
    ensures after.value == x;
} by {
    execute();
    simp();
}
```

```expect
pass
```
