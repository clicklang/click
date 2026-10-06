# A non-strict premise is insufficient

```click
theorem refused(left: int32, right: int32) {
    requires left <= right;
    ensures to_integer(left) < to_integer(right) by {
        apply(int32_less_than_to_integer(left, right));
    }
}
```

```expect
fail: int32_less_than_to_integer
```
