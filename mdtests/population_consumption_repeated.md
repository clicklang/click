# Reject repeated at consuming close

```c filename=negative_consumption.c
struct counter { unsigned int value; };
unsigned int contribute_early(struct counter *p) {
    p->value = p->value + 1u;
    p->value = p->value + 1u;
    return p->value;
}
```

```click resource_semantics=authority
verifying "negative_consumption.c";
resource remaining(p: struct counter*) {}
resource control(p: struct counter*) {
    owns authority(remaining(p));
    owns p->value;
    fact count(remaining(p)) <= 3;
    fact p->value == 3 - count(remaining(p));
}
uint32 contribute_early(struct counter* p) {
    owns control(p);
    owns 2 of remaining(p);
    consumes remaining(p);
    requires count(remaining(p)) > 1;
} by {
    open(control(p)) {
        have old(count(remaining(p))) >= 3 by simp;
        have old(count(remaining(p))) <= 3 by simp;
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
            arithmetic() using { count(remaining(p)) > 1; count(remaining(p)) <= 3; old(count(remaining(p))) >= 3; old(count(remaining(p))) <= 3; }
        }
        unfold(remaining(p));
        step();
    }
    open(control(p)) {
        have (3 - (old(count(remaining(p))) - 1)) + 1 == 3 - (old(count(remaining(p))) - 2) by {
            arithmetic() using { old(count(remaining(p))) >= 3; old(count(remaining(p))) <= 3; }
        }
        unfold(remaining(p)); step();
    }
    open(control(p)) { step(); }
    simp();
}
```

```expect
fail: missing resource fact `owns remaining(p) (quantity 2)`
```
