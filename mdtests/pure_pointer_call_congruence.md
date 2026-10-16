# Pointer-valued calls share typed model congruence

```click
spec enum Handle { None, Some(int32*) }
function handle_pointer(handle: Handle) -> int32* {
    match handle {
        Handle::None => 0,
        Handle::Some(p) => p,
    }
}
theorem pointer_alias(left: Handle, right: Handle, held: int32*) {
    requires left == right;
    requires held == handle_pointer(left);
    ensures held == handle_pointer(right) by { assumption(); }
}
```

```expect
pass
```
