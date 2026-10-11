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
        rewrite(b == Box::Box(n));
        normalize();
    }
}
```

```expect
fail: `normalize` goal did not normalize to true
```
