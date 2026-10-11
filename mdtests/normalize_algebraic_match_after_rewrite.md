# Algebraic match after rewriting its scrutinee

Constructor selection also substitutes C scalar, pointer,
and algebraic fields into an algebraic result. Unknown matches and pure calls
remain symbolic.

```c filename=payload.c
struct node { int value; };
```

```click
verifying "payload.c";
spec enum Color { Black, Red }
function choose(c: Color) -> Color {
    match c { Color::Black => Color::Red, Color::Red => Color::Black, }
}
theorem selected(c: Color) {
    requires c == Color::Black;
    ensures choose(c) == Color::Red by {
        unfold(choose(c));
        rewrite(c == Color::Black);
        normalize();
    }
}
spec enum Payload { Empty, At(int32, struct node*, Color) }
function repack(v: Payload) -> Payload {
    match v {
        Payload::Empty => Payload::Empty,
        Payload::At(n, p, c) => Payload::At(n, p, c),
    }
}
theorem payload(v: Payload, n: int32, p: struct node*, c: Color) {
    requires v == Payload::At(n, p, c);
    ensures repack(v) == Payload::At(n, p, c) by {
        unfold(repack(v));
        rewrite(v == Payload::At(n, p, c));
        normalize();
    }
}
```

```expect
pass
```
