# A function's owned binder takes the instance a call produced

`set_and_get` owns a `cell_at(c)` under the name `cell`. `execute()` runs
both calls: the first consumes the instance `cell` holds, and each produces a
new one. No proof step names the last, so it is held under no name; at the
exit, the owned binder `cell`, whose own instance is gone, takes it as the
only `cell_at` instance there, and the clause checks its arguments.

```c filename=owned_binder_takes_the_call_result.c
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
verifying "owned_binder_takes_the_call_result.c";

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
    owns cell: cell_at(c);
    ensures result == x;
    ensures cell.value == x;
} by {
    execute();
    simp();
}
```

```expect
pass
```
