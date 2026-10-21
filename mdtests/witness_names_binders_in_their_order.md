# A multi-binder `witness` names binders in their declared order

`witness { x: 3, y: 4 }` instantiates `x`, then `y`, each against the goal's
outermost binder. Writing the binders in another order is refused at the
first one that is not outermost.

```click
theorem witness_out_of_order() {
    ensures exists (x: int32, y: int32) { x == 3 and y == 4 } by {
        witness { y: 4, x: 3 };
        both { normalize(); } and { normalize(); }
    }
}
```

```expect
fail: goal binds `x`, but proof provided witness `y`
```
