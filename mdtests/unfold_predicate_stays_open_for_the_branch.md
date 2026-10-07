# unfolding a predicate keeps it open for the branch

`unfold(small)` names the predicate, not one call. It opens every instance
at once and the predicate stays transparent for the rest of the branch:
`small(a)` and `small(b)` both yield their bounds, and the later goal
`small(c)`, which is not a fact, is proved against its body by `assumption()`.

```click
predicate small(x: int32) { 0 <= x and x <= 5 }

theorem unfold_stays_open(a: int32, b: int32, c: int32) {
    requires small(a);
    requires small(b);
    requires 0 <= c;
    requires c <= 5;
    ensures 0 <= a and 0 <= b by {
        unfold(small);
        have small(c) by assumption();
        assumption();
    }
}
```

```expect
pass
```
