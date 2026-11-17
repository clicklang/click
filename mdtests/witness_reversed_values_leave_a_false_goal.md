# Positional witnesses use the declared binder order

`witness(3, 4)` instantiates `x`, then `y`, each against the goal's
outermost binder. Writing the binders in another order is refused at the
first one that is not outermost.

```click
theorem witness_reversed_values() {
    ensures exists (x: int32, y: int32) { x == 3 and y == 4 } by {
        witness(4, 3);
        both { normalize(); } and { normalize(); }
    }
}
```

```expect
fail:
```
