# The observation bridge retains its width

```click
theorem refused(left: int64, right: int64) {
    requires left < right;
    ensures to_integer(left) < to_integer(right) by {
        apply(int32_less_than_to_integer(left, right));
    }
}
```

```expect
fail: int32_less_than_to_integer
```
