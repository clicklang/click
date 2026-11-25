# An Integer match cannot invent a different payload

```click
spec enum Box { Box(Integer) }
function identity(b: Box) -> Box {
    match b { Box::Box(n) => Box::Box(n), }
}
theorem wrong(b: Box, n: Integer) {
    requires b == Box::Box(n);
    ensures identity(b) == Box::Box(n + 1) by {
        unfold(identity(b));
        rewrite(b, Box::Box(n));
        close();
    }
}
```

```expect
fail: could not establish `match Box::Box(n) { Box::Box(n) => Box::Box(n) } == Box::Box((n + 1))`
```
