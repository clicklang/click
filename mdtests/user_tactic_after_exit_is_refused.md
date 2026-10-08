# a tactic is applied before the function exits

In this release a tactic application changes the resources the proof holds
before the function returns. Applying one after the last statement has run is
refused.

```c filename=user_tactic_after_exit_is_refused.c
struct pr { int32 a; int32 b; };

void user(struct pr *p) {
}
```

```click
verifying "user_tactic_after_exit_is_refused.c";

resource both(p: struct pr*) {
    field tag: int32;
    owns p->a;
    owns p->b;
}

resource first(p: struct pr*) {
    field tag: int32;
    owns p->a;
}

resource second(p: struct pr*) {
    field tag: int32;
    owns p->b;
}

tactic divide(p: struct pr*) {
    consumes x: both(p);
    produces y: first(p);
    produces z: second(p);
    ensures y.tag == 7;
} by {
    unfold(x);
    let y = fold(first(p), { tag: 7 });
    let z = fold(second(p), { tag: 0 });
    have y.tag == 7;
}

void user(struct pr* p) {
    consumes x: both(p);
    produces y: first(p);
    produces z: second(p);
} by {
    step();
    step();
    let { y: y, z: z } = divide(p, { x: x });
    simp();
}
```

```expect
fail: cannot run after execution already reached function exit
```
