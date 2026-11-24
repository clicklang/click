# Named intro names the introduced variable

Bare `intro()` introduces a universal's variable under the name its
quantifier wrote, which may be in a contract far from the proof. `let name = intro()` lets the proof choose: the variable is `row` from here on, in the
remaining goal and in every later step, for machine integer, mathematical
`Integer` and pointer binders alike, and for nested quantifiers.

```click
theorem int32_binder(n: int32) {
    requires forall (k: int32) { to_integer(k + 0) == to_integer(k) };
    ensures forall (j: int32) { 0 <= j implies to_integer(j + 0) == to_integer(j) } by {
        intro(row) {
            intro() {
                instantiate(forall (k: int32) { to_integer(k + 0) == to_integer(k) }, row);
                close();
            }
        }
    }
}

theorem integer_binder() {
    ensures forall (m: Integer) { m + 0 == m } by {
        intro(value) {
            have value + 0 == value by close() using {};
            close();
        }
    }
}

theorem pointer_binder(q: int32*) {
    ensures forall (p: int32*) { p == p } by {
        intro(cell) {
            have cell == cell by close();
            close();
        }
    }
}

theorem nested_binders(n: int32) {
    ensures forall (a: int32) { forall (b: int32) { a < b implies a < b } } by {
        intro(x) {
            intro(y) {
                intro() {
                    have x < y by close();
                    close();
                }
            }
        }
    }
}
```

```expect
pass
```
