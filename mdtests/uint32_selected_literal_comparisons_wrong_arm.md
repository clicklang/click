# Literal comparison reconstruction does not prove a false bound

```click
theorem wrong_selected_literal_bound(x: uint32) {
    requires x == 10u32;
    ensures to_integer(if x == 9u32 { x } else { 3u32 }) <= 2 by {
        rewrite(x, 10u32);
        normalize();
    }
}
```

```expect
fail: did not normalize to true
```
