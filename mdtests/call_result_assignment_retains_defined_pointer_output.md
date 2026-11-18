# Assigning a call result retains its defined pointer output

The callee initializes `*slot`. Assigning its scalar result to a local does
not change that pointer cell, so its explicit definedness output remains
available at the next statement.

```c filename=pointer_output.c
extern int reset(int **slot);
int caller(int **slot) {
    int ignored;
    ignored = reset(slot);
    return 0;
}
```

```click
verifying "pointer_output.c";
extern int32 reset(int32 **slot) {
    owns *slot;
    ensures defined(*slot);
    ensures *slot == 0;
    ensures result == 0;
}
int32 caller(int32 **slot) {
    owns *slot;
    ensures defined(*slot);
    ensures result == 0;
} by {
    step();
    step();
    have at(statement(1).call(0).exit, defined(*slot)) by { known(); }
    have separate(memory(ignored), memory(*slot)) by { known(); }
    step();
    have separate(statement(1).assignment(ignored, 0).footprint, memory(*slot)) by {
        normalize() using { separate(memory(ignored), memory(*slot)); };
    }
    have defined(*slot) by {
        preserve(memory(*slot), statement(1).assignment(ignored, 0));
    }
    step_until(function.exit);
    have defined(*slot) by { solve(); }
}
```

```expect
pass
```
