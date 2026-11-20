# A scoped open restores a proof-local resource

The instance was folded before the scope began. After it closes, the proof
can read the original field and unfold that same instance.

```c filename=open_named_local.c
int32 read_local(int32* p) {
    int32 loaded = *p;
    return loaded;
}
```

```click
verifying "open_named_local.c";

resource exact_cell(p: int32*) {
    field value: int32;
    owns *p;
    fact *p == value;
}

int32 read_local(int32* p) {
    owns *p;
    requires *p == 7;
    ensures result == 7;
} by {
    let c = fold(exact_cell(p), { value: 7 }) by { known(); }
    with(c) { step(); }
    have c.value == 7 by { known(); }
    unfold(c);
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
