# An int32 order comparison keeps its match

```click
spec enum Packet { Empty, Full(int32) }

theorem written_lt() {
    ensures forall (unused: Integer) {
        (match Packet::Full(7) { Packet::Empty => 0, Packet::Full(n) => n }) < 8
    } by { intro(); normalize(); }
}

theorem written_le() {
    ensures forall (unused: Integer) {
        0 <= (match Packet::Empty { Packet::Empty => 0, Packet::Full(n) => n })
    } by { intro(); normalize(); }
}

theorem written_gt() {
    ensures forall (unused: Integer) {
        (match Packet::Full(-7) { Packet::Empty => 0, Packet::Full(n) => n }) > -8
    } by { intro(); known(); }
}

theorem written_ge() {
    ensures forall (unused: Integer) {
        (match Packet::Full(7) { Packet::Empty => 0, Packet::Full(n) => n }) >= 7
    } by { intro(); normalize(); }
}

theorem rewritten_lt(p: Packet) {
    requires p == Packet::Full(7);
    ensures (match p { Packet::Empty => 0, Packet::Full(n) => n }) < 8 by {
        rewrite(p, Packet::Full(7));
        normalize();
    }
}
```

```expect
pass
```
