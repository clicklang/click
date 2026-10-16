# The false disjunction cannot justify the true arm

```click
function or_value(x: uint64, y: uint64) -> int32 {
    if x == 0 or y == 1 { 7 } else { 9 }
}
theorem wrong(x: uint64, y: uint64) {
    requires not(x == 0);
    requires not(y == 1);
    ensures or_value(x, y) == 7 by {
        unfold(or_value(x, y)); normalize() using { not(x == 0); not(y == 1); };
    }
}
```

```expect
fail: did not normalize to true
```
