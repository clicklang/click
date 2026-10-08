# intro as names the introduced variable

Bare `intro()` introduces a universal's variable under the name its
quantifier wrote, which may be in a contract far from the proof. `intro() as
name` lets the proof choose: the variable is `row` from here on, in the
remaining goal and in every later step, for machine integer, mathematical
`Integer` and pointer binders alike, and for nested quantifiers.

```click
theorem int32_binder(n: int32) {
    requires forall (k: int32) { k + 0 == k };
    ensures forall (j: int32) { 0 <= j implies j + 0 == j } by {
        intro() as row;
        intro();
        instantiate(forall (k: int32) { k + 0 == k }, row);
    }
}

theorem integer_binder() {
    ensures forall (m: Integer) { m + 0 == m } by {
        intro() as value;
        have value + 0 == value by arithmetic();
        assumption();
    }
}

theorem pointer_binder(q: int32*) {
    ensures forall (p: int32*) { p == p } by {
        intro() as cell;
        have cell == cell by normalize();
        assumption();
    }
}

theorem nested_binders(n: int32) {
    ensures forall (a: int32) { forall (b: int32) { a < b implies a < b } } by {
        intro() as x;
        intro() as y;
        intro();
        have x < y by assumption();
        assumption();
    }
}
```

```expect
pass
```
