# Ordinary counted resources account for two contributions

This is a sequential control for the shared-worker counter design, not a proof
of the pthread program. A population starts with three units backed by the
actual counter memory. Each contribution consumes one unit and increments the
counter; the retained final unit recovers the memory at value two.
Initialization works both through a function contract and directly after the
assignment, using `fold(3 of remaining(p))`. Consumption still occurs at function
boundaries in this control; the unchanged pthread program needs consumption
inside a mutex acquisition. No new syntax or built-in resources are used.

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
unsigned int local_initialize(struct counter *p) {
    p->value = 0u;
    contribute(p);
    contribute(p);
    return p->value;
}
```

```click
verifying "counted_resource_contribution_counter.c";
resource remaining(p: struct counter*) {
    owns p->value;
    fact count(remaining(p)) <= 3;
    fact p->value == 3 - count(remaining(p));
}
void initialize(struct counter* p) {
    consumes p->value;
    produces 3 of remaining(p);
} by {
    execute();
    fold(3 of remaining(p));
    simp();
}
void contribute(struct counter* p) {
    owns remaining(p);
    consumes remaining(p);
    requires count(remaining(p)) > 1;
} by {
    open(remaining(p)) {
        have count(remaining(p)) - 1 >= 1 by {
            arithmetic() using {
                count(remaining(p)) > 1;
                count(remaining(p)) <= 3;
            }
        }
        have (3 - count(remaining(p))) + 1 == 3 - (count(remaining(p)) - 1) by {
            arithmetic() using {
                count(remaining(p)) > 1;
                count(remaining(p)) <= 3;
            }
        }
        execute();
    }
    simp();
}
uint32 sequential(struct counter* p) {
    owns p->value;
    ensures result == 2;
} by {
    step();
    step();
    step();
    unfold(remaining(p));
    step();
    simp();
}
uint32 local_initialize(struct counter* p) {
    owns p->value;
    ensures result == 2;
} by {
    step();
    fold(3 of remaining(p));
    step();
    step();
    unfold(remaining(p));
    step();
    simp();
}
```

```expect
pass
```
