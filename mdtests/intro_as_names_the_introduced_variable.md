# Named intro names the introduced variable

Use `intro(row) { ... }` to choose the name for an introduced variable. The
name is available throughout the block for machine integer, mathematical
`Integer`, and pointer binders.

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
