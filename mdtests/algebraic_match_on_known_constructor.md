# Algebraic matches retain a written or rewritten constructor

```click
spec enum Packet { Empty, Full(int32) }
spec enum Output { NoValue, Value(int32) }

theorem written() {
    ensures forall (unused: Integer) {
        (match Packet::Full(7) {
            Packet::Empty => Output::NoValue,
            Packet::Full(n) => Output::Value(n),
        }) == Output::Value(7)
    } by { intro(); normalize(); }
}

theorem rewritten(p: Packet) {
    requires p == Packet::Full(7);
    ensures (match p {
        Packet::Empty => Output::NoValue,
        Packet::Full(n) => Output::Value(n),
    }) == Output::Value(7) by {
        rewrite(p, Packet::Full(7));
        normalize();
    }
}
```

```expect
pass
```
