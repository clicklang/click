# Signed Integer observation bridges

Exact signed observations preserve and reflect non-strict order. A proved
Integer range can therefore bound a native narrowed result without inferring
an ambient machine range. The int64 equality bridge preserves the whole width.

```click
theorem reflect32(left: int32, right: int32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by apply(int32_less_equal_of_to_integer(left, right));
}
theorem preserve64(left: int64, right: int64) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by apply(int64_less_equal_to_integer(left, right));
}
theorem reflect64(left: int64, right: int64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by apply(int64_less_equal_of_to_integer(left, right));
}
theorem equal64(left: int64, right: int64) {
    requires to_integer(left) == to_integer(right);
    ensures left == right by apply(int64_equal_of_to_integer(left, right));
}
```

```expect
pass
```
