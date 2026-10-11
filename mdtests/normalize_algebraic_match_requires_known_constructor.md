# A symbolic match does not select an arm

```click
spec enum Color { Black, Red }
function choose(c: Color) -> Color {
    match c { Color::Black => Color::Red, Color::Red => Color::Black, }
}
theorem unknown(c: Color) {
    ensures choose(c) == Color::Red by {
        unfold(choose(c));
        normalize();
    }
}
```

```expect
fail: normalize
```
