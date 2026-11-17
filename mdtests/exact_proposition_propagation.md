# Exact Boolean consequences are available without solver search

```click
theorem exact_disjunction(a: int32, b: int32) {
    requires a == 0 or b == 0;
    requires not (a == 0);
    ensures b == 0 by known();
}

theorem exact_implication(a: int32, b: int32) {
    requires a == 0 implies b == 0;
    requires a == 0;
    ensures b == 0 by known();
}

theorem exact_conjunctive_guard(a: int32, b: int32, c: int32, d: int32) {
    requires a == 0 and b == 0 implies c == 0;
    requires c == 0 implies d == 0;
    requires a == 0;
    requires b == 0;
    ensures d == 0 by known();
}

theorem exact_rule_added_later(a: int32, b: int32) {
    requires a == 0;
    requires forall (k: int32) { k == 0 implies b == 0 };
    ensures b == 0 by {
        instantiate(forall (k: int32) { k == 0 implies b == 0 }, a);
        known();
    }
}
```

```expect
pass
```
