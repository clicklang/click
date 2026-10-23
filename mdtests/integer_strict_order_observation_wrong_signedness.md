# An observation theorem retains its signedness

```click
theorem strict_observation(left: int32, right: int32) {
    requires left < right;
    ensures to_integer(left) < to_integer(right) by auto();
}

theorem refused(left: uint32, right: uint32) {
    requires left < right;
    ensures to_integer(left) < to_integer(right) by {
        apply(strict_observation(left, right));
    }
}
```

```expect
fail: strict_observation
```
