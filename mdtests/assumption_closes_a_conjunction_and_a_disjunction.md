# assumption closes a conjunction and a disjunction

`assumption()` closes a goal that follows directly from facts. A conjunction
follows when every side does and a disjunction when one side does, at any
nesting, so the conjunction of two preconditions needs no separate tactic.

```click
theorem assumption_closes_connectives(x: int32, y: int32) {
    requires 0 <= x;
    requires y == 3;
    ensures 0 <= x and y == 3 by assumption();
    ensures x < 0 or y == 3 by assumption();
    ensures 0 <= x or y == 7 by assumption();
    ensures (x < 0 or 0 <= x) and (y == 3 and 0 <= x) by assumption();
}
```

```expect
pass
```
