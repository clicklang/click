# A named introduction hides a fact of the same name

Inside `intro(five) { ... }`, the introduced variable hides the fact named
by `have five: P`. The fact remains available by its proposition.

```click
theorem t(x: int32) {
    requires x == 5;
    ensures forall (k: int32) { x == 5 } by {
        have five: x == 5;
        intro(five) {
            have five == five by close();
            close() using { x == 5; };
        }
    }
}
```

```expect
pass
```
