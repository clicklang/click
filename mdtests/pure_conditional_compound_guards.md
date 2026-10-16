# Pure scalar conditionals retain compound guards for explicit normalization

```click
function or_value(x: uint64, y: uint64) -> int32 {
    if x == 0 or y == 1 { 7 } else { 9 }
}
function and_value(x: uint64, y: uint64) -> int32 {
    if x == 0 and not(y == 1) { 7 } else { 9 }
}
function negated_value(x: uint64, y: uint64) -> int32 {
    if not(x == 0 or y == 1) { 7 } else { 9 }
}
theorem or_left(x: uint64, y: uint64) {
    requires x == 0;
    ensures or_value(x, y) == 7 by {
        unfold(or_value(x, y)); normalize() using { x == 0; };
    }
}
theorem or_right(x: uint64, y: uint64) {
    requires not(x == 0);
    requires y == 1;
    ensures or_value(x, y) == 7 by {
        unfold(or_value(x, y)); normalize() using { not(x == 0); y == 1; };
    }
}
theorem or_neither(x: uint64, y: uint64) {
    requires not(x == 0);
    requires not(y == 1);
    ensures or_value(x, y) == 9 by {
        unfold(or_value(x, y)); normalize() using { not(x == 0); not(y == 1); };
    }
}
theorem and_both(x: uint64, y: uint64) {
    requires x == 0;
    requires not(y == 1);
    ensures and_value(x, y) == 7 by {
        unfold(and_value(x, y)); normalize() using { x == 0; not(y == 1); };
    }
}
theorem and_left_false(x: uint64, y: uint64) {
    requires not(x == 0);
    ensures and_value(x, y) == 9 by {
        unfold(and_value(x, y)); normalize() using { not(x == 0); };
    }
}
theorem and_right_false(x: uint64, y: uint64) {
    requires y == 1;
    ensures and_value(x, y) == 9 by {
        unfold(and_value(x, y)); normalize() using { y == 1; };
    }
}
theorem negated_neither(x: uint64, y: uint64) {
    requires not(x == 0);
    requires not(y == 1);
    ensures negated_value(x, y) == 7 by {
        unfold(negated_value(x, y)); normalize() using { not(x == 0); not(y == 1); };
    }
}
```

```expect
pass
```
