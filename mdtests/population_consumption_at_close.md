# An open scope can fulfill one declared consumption before return

An explicit member consumption inside an open control scope lowers Count once.
Closing restores the counter invariant at that new Count; reopening the control
permits a later read without consuming again. Nested calls and either branch
preserve that effect. The caller starts with empty authority, creates three
members, calls the contribution helper twice, and proves exact two before
consuming the final member and retiring authority. C source is unchanged.

```c filename=early_consumption.c
struct counter { unsigned int value; };
unsigned int contribute_early(struct counter *p) {
    p->value = p->value + 1u;
    return p->value;
}
unsigned int read_current(struct counter *p) { return p->value; }
unsigned int contribute_nested(struct counter *p) {
    p->value = p->value + 1u;
    return read_current(p);
}
unsigned int contribute_branch(struct counter *p, int report) {
    p->value = p->value + 1u;
    if (report) return p->value;
    return 0u;
}
unsigned int sequential_early(struct counter *p) {
    p->value = 0u;
    contribute_early(p);
    contribute_early(p);
    return p->value;
}
```

```click resource_semantics=authority
verifying "early_consumption.c";
authorized resource remaining(p: struct counter*) {}
resource storage(p: struct counter*) {
    owns p->value;
    owns authority(remaining(p));
    fact count(remaining(p)) == 0;
}
resource control(p: struct counter*) {
    owns authority(remaining(p));
    owns p->value;
    fact count(remaining(p)) <= 3;
    fact p->value == 3 - count(remaining(p));
}
uint32 contribute_early(struct counter* p) {
    owns control(p);
    consumes remaining(p);
    requires count(remaining(p)) > 1;
    ensures count(remaining(p)) == old(count(remaining(p))) - 1;
    ensures p->value == old(p->value) + 1;
} by {
    open(control(p)) { have count(remaining(p)) <= 3; }
    open(control(p)) {
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
        have count(remaining(p)) - 1 <= 3 by {
            arithmetic() using { count(remaining(p)) > 1; count(remaining(p)) <= 3; }
        }
        unfold(remaining(p));
        step();
    }
    open(control(p)) { step(); }
    simp();
}
uint32 read_current(struct counter* p) {
    owns control(p);
} by {
    open(control(p)) { execute(); }
    simp();
}
uint32 contribute_nested(struct counter* p) {
    owns control(p);
    consumes remaining(p);
    requires count(remaining(p)) > 1;
    ensures count(remaining(p)) == old(count(remaining(p))) - 1;
    ensures p->value == old(p->value) + 1;
} by {
    open(control(p)) {
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
        have count(remaining(p)) - 1 <= 3 by {
            arithmetic() using { count(remaining(p)) > 1; count(remaining(p)) <= 3; }
        }
        unfold(remaining(p));
        step();
    }
    step();
    step();
    simp();
}
uint32 contribute_branch(struct counter* p, int32 report) {
    owns control(p);
    consumes remaining(p);
    requires count(remaining(p)) > 1;
    ensures count(remaining(p)) == old(count(remaining(p))) - 1;
    ensures p->value == old(p->value) + 1;
} by {
    open(control(p)) {
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
        have count(remaining(p)) - 1 <= 3 by {
            arithmetic() using { count(remaining(p)) > 1; count(remaining(p)) <= 3; }
        }
        unfold(remaining(p));
        step();
    }
    if report != 0 {
        open(control(p)) { execute(); }
        simp();
    } else {
        execute();
        simp();
    }
}
uint32 sequential_early(struct counter* p) {
    consumes storage(p);
    produces p->value;
    ensures result == 2;
} by {
    unfold(storage(p));
    step();
    fold(3 of remaining(p));
    fold(control(p));
    step();
    step();
    unfold(control(p));
    unfold(remaining(p));
    unfold(authority(remaining(p)));
    step();
    simp();
}
```

```expect
pass
```
