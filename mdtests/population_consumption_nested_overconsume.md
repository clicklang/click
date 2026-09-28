# A nested call cannot hide a second consumption at return

```c filename=overconsume.c
struct counter { unsigned int value; };
unsigned int contribute_early(struct counter *p) {
    p->value = p->value + 1u;
    return p->value;
}
unsigned int overconsume(struct counter *p) {
    p->value = p->value + 1u;
    return contribute_early(p);
}
```

```click
verifying "overconsume.c";
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
uint32 overconsume(struct counter* p) {
    owns 2 of remaining(p);
    consumes remaining(p);
    requires count(remaining(p)) > 2;
} by {
    have count(remaining(p)) > 1 by { arithmetic() using { count(remaining(p)) > 2; } }
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
        have count(remaining(p)) - 1 > 1 by { arithmetic() using { count(remaining(p)) > 2; count(remaining(p)) <= 3; } }
        step();
    }
    step();
    step();
    simp();
}
```

```expect
fail: missing resource fact `owns remaining(p) (quantity 2)`
```
