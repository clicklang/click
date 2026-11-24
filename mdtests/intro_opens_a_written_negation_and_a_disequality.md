# Refuting a condition or equality with a proof if

A proof `if` on the denied proposition puts it in scope in one arm.
That arm can close with `contradiction`; the other arm has the goal as a fact.

```c filename=intro_opens_a_written_negation_and_a_disequality.c
void unused(void) {}
```

```click
verifying "intro_opens_a_written_negation_and_a_disequality.c";

theorem written_negation(n: int32) {
    requires n == 0;
    ensures not (n == 1) by {
        if n == 1 {
            have false by { close() using { n == 0; n == 1; }; }
            contradiction();
        } else {
            close();
        }
    }
}

theorem disequality(a: Integer, b: Integer) {
    requires a < b;
    ensures a != b by {
        if a == b {
            have false by { close() using { a < b; a == b; }; }
            contradiction();
        } else {
            close();
        }
    }
}

theorem written_order_negation(x: int32, y: int32) {
    requires x < y;
    ensures not (x >= y) by {
        if x >= y {
            contradiction(x < y);
        } else {
            close();
        }
    }
}
```

```expect
pass
```
