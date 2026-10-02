# Equal signed int32 observations identify the machine values

```click
theorem integer_equality_recovers_int32(left: int32, right: int32) {
    requires to_integer(left) == to_integer(right);
    ensures left == right by {
        apply(int32_equal_of_to_integer(left, right)) using {
            to_integer(left) == to_integer(right);
        }
        assumption();
    }
}
```

```expect
pass
```
