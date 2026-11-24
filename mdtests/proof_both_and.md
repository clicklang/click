# Exact conjunction subproofs

Each arm inherits the parent assumptions and has its own proof scope.
Nested conjunctions can use a flat list in any order. Universal arms keep their binders.

```click
theorem reflexive_pair(x: int32) {
    ensures x == x and (x <= x and x >= x) by {
        all {
            x >= x => { close(); }
            x == x => { close(); }
            x <= x => { close(); }
        }
    }
}

theorem quantified_pair() {
    ensures (forall (i: int32) { i == i }) and
            (forall (j: int32) { j <= j }) by {
        all {
            forall (i: int32) { i == i } => { intro() { close(); } }
            forall (j: int32) { j <= j } => { intro() { close(); } }
        }
    }
}
theorem repeated_conjunct(x: int32) {
    ensures x <= x and x <= x by {
        all {
            x <= x => { close(); }
            x <= x => { close(); }
        }
    }
}
```

```expect
pass
```
