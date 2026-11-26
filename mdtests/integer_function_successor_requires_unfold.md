# Integer pure function calls remain opaque without unfold

```click
function successor(z: Integer) -> Integer {
    z + 1
}

theorem successor_requires_unfold(z: Integer) {
    ensures successor(z) == z + 1 by {
        close() using {};
    }
}
```

```expect
fail: `close() using` could not prove the current goal from only its listed premises
```
