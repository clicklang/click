# An integer body for a `Bool` function is refused

A `-> Bool` body produces only `Bool` values. An integer is not read as a
truth value, so `1`, or a conditional with an integer branch, is a type
error rather than C's nonzero test.

```click
function flagged(x: int32) -> Bool {
    if x > 0 { true } else { 0 }
}
```

```expect
fail: function `flagged` returns Bool, but its body can produce `0` of type int32
```
