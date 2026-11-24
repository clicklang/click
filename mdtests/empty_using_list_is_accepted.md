# an empty using list is accepted

A goal that holds on its own needs no premises, and each tactic that takes a
`using` list accepts an empty one.

```click
theorem reflexive(x: int32) {
    ensures x == x by known();
}

theorem empty_using_lists(x: int32, k: int32) {
    requires forall (j: int32) { j + 0 == j };
    ensures x == x by { close() using { }; }
    ensures (x & 255) <= 255 by { close() using { }; }
    ensures x + 0 == x + 0 by { close() using { }; }
    ensures x == x by { apply(reflexive(x)); }
    ensures k + 0 == k by {
        instantiate(forall (j: int32) { j + 0 == j }, k);
        known();
    }
}
```

```expect
pass
```
