# Pure scalar conditionals select arms through compound guards

Compound guards lower to short-circuit conditionals that return 0 or 1.
The proofs name the equations for those values before selecting the outer arm.

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
theorem or_guard_is_false(x: uint64, y: uint64) {
    requires not(x == 0);
    requires not(y == 1);
    ensures (if x == 0u64 { 1 } else { if y == 1u64 { 1 } else { 0 } }) != 1 by {
        have (if x == 0u64 { 1 } else { if y == 1u64 { 1 } else { 0 } }) == 0 by {
            have (if y == 1u64 { 1 } else { 0 }) == 0 by { close(); }
            rewrite((if y == 1u64 { 1 } else { 0 }), 0);
            close();
        }
        rewrite((if x == 0u64 { 1 } else { if y == 1u64 { 1 } else { 0 } }), 0);
        close();
    }
}

theorem or_left(x: uint64, y: uint64) {
    requires x == 0;
    ensures or_value(x, y) == 7 by {
        unfold(or_value(x, y));
        rewrite(x, 0);
        close();
    }
}
theorem or_right(x: uint64, y: uint64) {
    requires not(x == 0);
    requires y == 1;
    ensures or_value(x, y) == 7 by {
        unfold(or_value(x, y));
        rewrite(y, 1);
        close();
    }
}
theorem or_neither(x: uint64, y: uint64) {
    requires not(x == 0);
    requires not(y == 1);
    ensures or_value(x, y) == 9 by {
        unfold(or_value(x, y));
        apply(or_guard_is_false(x, y));
        close();
    }
}
theorem and_both(x: uint64, y: uint64) {
    requires x == 0;
    requires not(y == 1);
    ensures and_value(x, y) == 7 by {
        unfold(and_value(x, y));
        have (if x == 0u64 { if y == 1u64 { 0 } else { 1 } } else { 0 }) == 1 by {
            have (if y == 1u64 { 0 } else { 1 }) == 1 by { close(); }
            rewrite((if y == 1u64 { 0 } else { 1 }), 1);
            close();
        }
        close();
    }
}
theorem and_left_false(x: uint64, y: uint64) {
    requires not(x == 0);
    ensures and_value(x, y) == 9 by {
        unfold(and_value(x, y));
        have (if x == 0u64 { if y == 1u64 { 0 } else { 1 } } else { 0 }) != 1 by {
            have (if x == 0u64 { if y == 1u64 { 0 } else { 1 } } else { 0 }) == 0 by { close(); }
            rewrite((if x == 0u64 { if y == 1u64 { 0 } else { 1 } } else { 0 }), 0);
            close();
        }
        close();
    }
}
theorem and_right_false(x: uint64, y: uint64) {
    requires y == 1;
    ensures and_value(x, y) == 9 by {
        unfold(and_value(x, y));
        rewrite(y, 1);
        close();
    }
}
theorem negated_neither(x: uint64, y: uint64) {
    requires not(x == 0);
    requires not(y == 1);
    ensures negated_value(x, y) == 7 by {
        unfold(negated_value(x, y));
        apply(or_guard_is_false(x, y));
        close();
    }
}
```

```expect
pass
```
