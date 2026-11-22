# `let name = intro()` hides a fact of the same name

The newest binding of a name wins wherever the name is read. A variable
introduced by `let five = intro()` hides the fact named by `have five: P` for
the rest of its block, so a citation of `five` there reads the variable,
not the fact. The fact is still available by its proposition.

```click
theorem t(x: int32) {
    requires x == 5;
    ensures forall (k: int32) { x == 5 } by {
        have five: x == 5;
        let five = intro();
        have five == five by known();
        solve() using { x == 5; };
    }
}
```

```expect
pass
```
