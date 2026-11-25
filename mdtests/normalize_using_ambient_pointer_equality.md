# Pointer equality through the current equality graph

After introducing pointer binders and equality assumptions, `close()` checks
their transitive equality.

```click
theorem pointer_transitivity() {
    ensures forall (a: int32*) { forall (b: int32*) { forall (c: int32*) {
        a == b implies (b == c implies a == c)
    } } } by {
        intro() {
            intro() {
                intro() {
                    intro() {
                        intro() {
                            close();
                        }
                    }
                }
            }
        }
    }
}
```

```expect
pass
```
