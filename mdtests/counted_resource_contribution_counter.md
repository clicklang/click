# Ordinary counted resources account for two contributions

This is a sequential control for the shared-worker counter design, not a proof
of the pthread program. Empty contribution members grant one increment each;
an ordinary control owns counter memory and authority, relating the stored
value to the remaining population. Storage supplies initially empty authority.
After two contributions, cleanup consumes the final member and retires the
empty authority before returning the counter memory. Symbolic whole-population
cleanup and direct initialization preserve the same C and result claims.

```c filename=counted_resource_contribution_counter.c
struct counter { unsigned int value; };
void initialize(struct counter *p) { p->value = 0u; }
void contribute(struct counter *p) { p->value = p->value + 1u; }
unsigned int sequential(struct counter *p) {
    initialize(p);
    contribute(p);
    contribute(p);
    return p->value;
}
unsigned int cleanup_known(struct counter *p, int n) { return p->value; }
unsigned int cleanup_three(struct counter *p) {
    p->value = 0u;
    return p->value;
}
unsigned int cleanup_two(struct counter *p) {
    p->value = 0u;
    contribute(p);
    return p->value;
}
unsigned int local_initialize(struct counter *p) {
    p->value = 0u;
    contribute(p);
    contribute(p);
    return p->value;
}
```

```click resource_semantics=authority
verifying "counted_resource_contribution_counter.c";
resource remaining(p: struct counter*) {}
resource storage(p: struct counter*) {
    owns p->value;
    owns authority(remaining(p));
    fact count(remaining(p)) == 0;
}
resource control(p: struct counter*) {
    owns p->value;
    owns authority(remaining(p));
    fact count(remaining(p)) <= 3;
    fact p->value == 3 - count(remaining(p));
}
void initialize(struct counter* p) {
    consumes storage(p);
    produces control(p);
    produces 3 of remaining(p);
    ensures p->value == 0;
    ensures count(remaining(p)) == 3;
} by {
    unfold(storage(p));
    step();
    fold(3 of remaining(p));
    fold(control(p));
    execute(); simp();
}
void contribute(struct counter* p) {
    owns control(p);
    consumes remaining(p);
    requires count(remaining(p)) > 1;
    ensures count(remaining(p)) == old(count(remaining(p))) - 1;
    ensures p->value == old(p->value) + 1;
} by {
    open(control(p)) {
        have count(remaining(p)) - 1 >= 1 by {
            arithmetic() using { count(remaining(p)) > 1; count(remaining(p)) <= 3; }
        }
        have (3 - count(remaining(p))) + 1 == 3 - (count(remaining(p)) - 1) by {
            arithmetic() using { count(remaining(p)) > 1; count(remaining(p)) <= 3; }
        }
        have count(remaining(p)) - 1 <= 3 by {
            arithmetic() using { count(remaining(p)) > 1; count(remaining(p)) <= 3; }
        }
        unfold(remaining(p));
        step();
    }
    execute(); simp();
}
uint32 sequential(struct counter* p) {
    consumes storage(p);
    produces p->value;
    ensures result == 2;
} by {
    step(); step(); step();
    unfold(control(p));
    unfold(remaining(p));
    unfold(authority(remaining(p)));
    execute(); simp();
}
uint32 cleanup_known(struct counter* p, int32 n) {
    consumes control(p);
    consumes n of remaining(p);
    requires n > 0;
    requires count(remaining(p)) == n;
    produces p->value;
    ensures result == 3 - n;
} by {
    unfold(control(p));
    unfold(n of remaining(p));
    unfold(authority(remaining(p)));
    execute(); simp();
}
uint32 cleanup_three(struct counter* p) {
    consumes storage(p);
    produces p->value;
    ensures result == 0;
} by {
    unfold(storage(p));
    step();
    fold(3 of remaining(p));
    unfold(3 of remaining(p));
    unfold(authority(remaining(p)));
    execute(); simp();
}
uint32 cleanup_two(struct counter* p) {
    consumes storage(p);
    produces p->value;
    ensures result == 1;
} by {
    unfold(storage(p));
    step();
    fold(3 of remaining(p));
    fold(control(p));
    step();
    unfold(control(p));
    unfold(2 of remaining(p));
    unfold(authority(remaining(p)));
    execute(); simp();
}
uint32 local_initialize(struct counter* p) {
    consumes storage(p);
    produces p->value;
    ensures result == 2;
} by {
    unfold(storage(p));
    step();
    fold(3 of remaining(p));
    fold(control(p));
    step(); step();
    unfold(control(p));
    unfold(remaining(p));
    unfold(authority(remaining(p)));
    execute(); simp();
}
```

```expect
pass
```
