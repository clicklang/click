# Every source arm must establish a part of the projection

```click
spec enum Walk { Active, Done }
function pending(w: Walk) -> int32 {
    match w { Walk::Active => 1, Walk::Done => 0, }
}
theorem project(a: Walk, b: Walk, x: int32, y: int32) {
    requires a == b;
    requires (pending(a) == 0 and x >= 5) or (y == 1 and x <= 5);
    ensures pending(b) == 0 or y == 2 by {
        extract(pending(b) == 0 or y == 2);
    }
}
```

```expect
fail: `extract` proposition is not a proper conjunct
```
