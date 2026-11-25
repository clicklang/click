# Constructor selection cannot choose another arm

```click
spec enum Color { Black, Red }
function choose(c: Color) -> Color {
    match c { Color::Black => Color::Red, Color::Red => Color::Black, }
}
theorem wrong(c: Color) {
    requires c == Color::Black;
    ensures choose(c) == Color::Black by {
        unfold(choose(c));
        rewrite(c, Color::Black);
        close();
    }
}
```

```expect
fail: could not establish `match Color::Black()
```
