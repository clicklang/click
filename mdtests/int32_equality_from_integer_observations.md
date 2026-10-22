# Equal signed int32 observations identify the machine values

```click
import click::integer;

theorem integer_equality_recovers_int32(left: int32, right: int32) {
    requires to_integer(left) == to_integer(right);
    ensures left == right;
}
```

```expect
pass
```
