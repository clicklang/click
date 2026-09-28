# An open scope can fulfill one declared consumption before return

The first close spends one unit and restores the invariant at the reduced
Count. Reopening permits the subsequent C read. The caller initializes three
units, calls this helper twice, and proves exact two, checking that return
neither loses nor duplicates the early effect.

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

```click
verifying "early_consumption.c";
resource remaining(p: struct counter*) {
    owns p->value;
    fact count(remaining(p)) <= 3;
    fact p->value == 3 - count(remaining(p));
}
uint32 contribute_early(struct counter* p) {
    owns remaining(p);
    consumes remaining(p);
    requires count(remaining(p)) > 1;
} by {
    open(remaining(p)) { have count(remaining(p)) <= 3 by { simp(); } }
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
        have count(remaining(p)) - 1 <= 3 by {
            arithmetic() using { count(remaining(p)) > 1; count(remaining(p)) <= 3; }
        }
        step();
    }
    open(remaining(p)) { step(); }
    simp();
}
uint32 read_current(struct counter* p) {
    owns remaining(p);
} by {
    open(remaining(p)) { execute(); }
    simp();
}
uint32 contribute_nested(struct counter* p) {
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
        have count(remaining(p)) - 1 <= 3 by {
            arithmetic() using { count(remaining(p)) > 1; count(remaining(p)) <= 3; }
        }
        step();
    }
    step();
    step();
    simp();
}
uint32 contribute_branch(struct counter* p, int32 report) {
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
        have count(remaining(p)) - 1 <= 3 by {
            arithmetic() using { count(remaining(p)) > 1; count(remaining(p)) <= 3; }
        }
        step();
    }
    if report != 0 {
        open(remaining(p)) { execute(); }
        simp();
    } else {
        execute();
        simp();
    }
}
uint32 sequential_early(struct counter* p) {
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
