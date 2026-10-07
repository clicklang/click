# A join interface reads a reassigned parameter where the arms end

The function overwrites its parameter `p` with `q` before the store. Each
arm of the proof `if` folds the slot at `p`, and `ensuring` names the slot
the same way.

An interface names what the proof holds where its arms end, so `p` there is
the pointer the arms folded at, not the argument the function was called
with. Read as the entry argument, the interface asked each arm for a slot at
an address neither had touched, and the join was refused as not having
established it.

```c filename=proof_if_ensuring_names_a_reassigned_parameter.c
struct cell { int32 value; };

int32 walk(struct cell *p, struct cell *q, int32 x) {
    p = q;
    p->value = 1;
    return 0;
}
```

```click
verifying "proof_if_ensuring_names_a_reassigned_parameter.c";

resource slot(p: struct cell*) {
    field model: int32;
    owns p->value;
    fact p->value == model;
}

int32 walk(struct cell* p, struct cell* q, int32 x) {
    requires q != 0;
    owns d: slot(q);
    ensures result == 0;
} by {
    step();
    if x <= 0 ensuring {
        owns d: slot(p);
    } then {
        unfold(d);
        step();
        let d = fold(slot(p), { model: 1 });
    } else {
        unfold(d);
        step();
        let d = fold(slot(p), { model: p->value });
    }
    step();
    simp();
}
```

```expect
pass
```
