# Integer matches on written constructors

```click
spec enum Choice { Empty, Full(Integer) }

function read_value(c: Choice) -> Integer {
    match c { Choice::Empty => 0, Choice::Full(n) => n + 1 }
}

theorem concrete(x: Integer) {
    ensures read_value(Choice::Full(x)) == x + 1 by {
        unfold(read_value(Choice::Full(x)));
        normalize();
    }
    ensures (match Choice::Full(x) { Choice::Empty => 0, Choice::Full(n) => n + 1 }) == x + 1 by {
        normalize();
    }
    ensures (match Choice::Empty { Choice::Empty => 0, Choice::Full(n) => n + 1 }) == 0 by {
        known();
    }
}

theorem symbolic(c: Choice, x: Integer) {
    requires c == Choice::Full(x);
    ensures read_value(c) == x + 1 by {
        unfold(read_value(c));
        rewrite(c, Choice::Full(x));
        normalize();
    }
}
```

```expect
pass
```
