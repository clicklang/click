# Positional witnesses instantiate a prefix of the existential binders

Batch arguments follow the goal's outermost binders. Single arguments can
leave the remaining existential goal open while an intermediate fact is proved.
Binder names do not appear in the tactic.

```click
theorem batch() {
    ensures exists (x: int32, y: int32) { x == 3 and y == 4 } by {
        witness(3, 4);
        solve();
    }
}
theorem partial() {
    ensures exists (renamed: int32, other: int32) { renamed == 3 and other == 4 } by {
        witness(3);
        have 4 == 4;
        witness(4);
        solve();
    }
}
theorem generated_binders() {
    ensures exists (binder(71): Integer, binder(72): Integer) {
        binder(71) == 3 and binder(72) == 4
    } by {
        witness(3, 4);
        solve();
    }
}
```

```expect
pass
```
