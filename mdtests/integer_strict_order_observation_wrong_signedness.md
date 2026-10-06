# The observation bridge retains its signedness

```click
theorem refused(left: uint32, right: uint32) {
    requires left < right;
    ensures to_integer(left) < to_integer(right) by {
        apply(int32_less_than_to_integer(left, right));
    }
}
```

```expect
fail: int32_less_than_to_integer
```
