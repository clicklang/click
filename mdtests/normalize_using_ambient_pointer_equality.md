# Normalization can query the current equality graph

After introducing pointer binders and equality assumptions, normalization
can query their transitive equality without citing either premise.

```click
theorem pointer_transitivity() {
    ensures forall (a: int32*) { forall (b: int32*) { forall (c: int32*) {
        a == b implies (b == c implies a == c)
    } } } by {
        intro();
        intro();
        intro();
        intro();
        intro();
        normalize() using { }
    }
}
```

```expect
pass
```
