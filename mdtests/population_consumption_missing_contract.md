# Reject missing contract at consuming close

```c filename=negative_consumption.c
struct counter { unsigned int value; };
unsigned int contribute_early(struct counter *p) {
    p->value = p->value + 1u;
    
    return p->value;
}
```

```click
verifying "negative_consumption.c";
resource remaining(p: struct counter*) {
    owns p->value;
    fact count(remaining(p)) <= 3;
    fact p->value == 3 - count(remaining(p));
}
uint32 contribute_early(struct counter* p) {
    owns remaining(p);
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
    open(remaining(p)) { step(); }
    simp();
}
```

```expect
fail: Requires `consumes remaining(p)`
```
