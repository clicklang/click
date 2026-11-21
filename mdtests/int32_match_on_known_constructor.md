# An int32 match keeps its comparison after rewriting

```click
spec enum Packet { Empty, Full(int32) }

theorem written() {
    ensures forall (unused: Integer) {
        (match Packet::Full(7) {
            Packet::Empty => 0,
            Packet::Full(n) => n,
        }) == 7
    } by { intro(); known(); }
}

theorem rewritten(p: Packet) {
    requires p == Packet::Full(7);
    ensures (match p {
        Packet::Empty => 0,
        Packet::Full(n) => n,
    }) == 7 by {
        rewrite(p, Packet::Full(7));
        known();
    }
}
```

```expect
pass
```
