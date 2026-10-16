# A compound guard without evidence cannot select a scalar arm

```click
function or_value(x: uint64, y: uint64) -> int32 {
    if x == 0 or y == 1 { 7 } else { 9 }
}
theorem unknown(x: uint64, y: uint64) {
    ensures or_value(x, y) == 7 by {
        unfold(or_value(x, y)); normalize();
    }
}
```

```expect
fail: did not normalize to true
```
