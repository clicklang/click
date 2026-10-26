# An observation theorem retains its width

```click
theorem strict_observation(left: int32, right: int32) {
    requires left < right;
    ensures to_integer(left) < to_integer(right);
}

theorem refused(left: int64, right: int64) {
    requires left < right;
    ensures to_integer(left) < to_integer(right) by {
        apply(strict_observation(left, right));
    }
}
```

```expect
fail: strict_observation
```
