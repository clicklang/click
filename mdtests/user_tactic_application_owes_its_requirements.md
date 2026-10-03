# a tactic application owes the tactic's requirements as available facts

`check_first` requires `p->a == 1`. An application is a simple step: it
searches for nothing, so the requirement must already be an available fact.
Here it is not, and the application is refused by naming it.

```c filename=user_tactic_application_owes_its_requirements.c
struct pr { int32 a; int32 b; };

void user(struct pr *p) {
}
```

```click
verifying "user_tactic_application_owes_its_requirements.c";

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


tactic check_first(p: struct pr*) {
    owns x: both(p);
    requires p->a == 1;
    ensures 1 == 1;
} by {
    have 1 == 1 by { simp(); }
}

void user(struct pr* p) {
    owns x: both(p);
} by {
    check_first(p) { x: x };
    step();
    step();
    simp();
}
```

```expect
fail: tactic `check_first` requires
```
