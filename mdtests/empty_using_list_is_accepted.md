# an empty using list is accepted

A goal that holds on its own needs no premises, and each tactic that takes a
`using` list accepts an empty one.

```click
theorem reflexive(x: int32) {
    ensures x == x by { normalize(); }
}

theorem empty_using_lists(x: int32, k: int32) {
    requires forall (j: int32) { j + 0 == j };
    ensures x == x by { simp() using { } }
    ensures (x & 255) <= 255 by { arithmetic() using { } }
    ensures x + 0 == x + 0 by { normalize() using { } }
    ensures x == x by { apply(reflexive(x)) using { } }
    ensures k + 0 == k by {
        instantiate(forall (j: int32) { j + 0 == j }, k) using { }
    }
}
```

```expect
pass
```
