# An inner Integer match cannot return a shadowed outer payload

```click
spec enum Box { Box(Integer) }
function shadow(b: Box, other: Box, n: Integer) -> Box {
    match b { Box::Box(n) => match other { Box::Box(n) => Box::Box(n), }, }
}
theorem wrong(b: Box, other: Box, n: Integer, m: Integer, ambient: Integer) {
    requires b == Box::Box(n);
    requires other == Box::Box(m);
    ensures shadow(b, other, ambient) == Box::Box(n) by {
        unfold(shadow(b, other, ambient));
        rewrite(b, Box::Box(n));
        rewrite(other, Box::Box(m));
        close();
    }
}
```

```expect
fail: could not establish `match Box::Box(n) { Box::Box(n) => match Box::Box(m) { Box::Box(n) => Box::Box(n) } } == Box::Box(n)`
```
