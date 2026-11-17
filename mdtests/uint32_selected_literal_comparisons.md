# Selected 32-bit literal comparison operands round-trip after rewriting

```click
theorem uint32_equal_guard(x: uint32) {
    requires x == 10u32;
    ensures to_integer(if x == 9u32 { x } else { 3u32 }) <= 100 by {
        rewrite(x, 10u32);
        normalize();
    }
    ensures 0 <= to_integer(if x == 9u32 { x } else { 3u32 }) by {
        rewrite(x, 10u32);
        normalize();
    }
}

theorem uint32_unequal_guard(x: uint32) {
    requires x == 9u32;
    ensures to_integer(if x != 9u32 { x } else { 3u32 }) <= 100 by {
        rewrite(x, 9u32);
        normalize();
    }
    ensures 0 <= to_integer(if x != 9u32 { x } else { 3u32 }) by {
        rewrite(x, 9u32);
        normalize();
    }
}

theorem int32_equal_guard(x: int32) {
    requires x == 10;
    ensures to_integer(if x == 9 { x } else { 3 }) <= 100 by {
        rewrite(x, 10);
        normalize();
    }
    ensures 0 <= to_integer(if x == 9 { x } else { 3 }) by {
        rewrite(x, 10);
        normalize();
    }
}

theorem int32_unequal_guard(x: int32) {
    requires x == 9;
    ensures to_integer(if x != 9 { x } else { 3 }) <= 100 by {
        rewrite(x, 9);
        normalize();
    }
    ensures 0 <= to_integer(if x != 9 { x } else { 3 }) by {
        rewrite(x, 9);
        normalize();
    }
}
```

```expect
pass
```
