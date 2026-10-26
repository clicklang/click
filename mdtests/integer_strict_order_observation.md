# Strict order of observed native values

```click
import click::integer;

theorem derived_strict_observer(left: int32, right: int32) {
    requires left < right;
    ensures to_integer(left) < to_integer(right) by {
        if to_integer(right) <= to_integer(left) {
            contradiction(left < right);
        } else {
            solve() using { not (to_integer(right) <= to_integer(left)); };
        }
    }
}
theorem strict_observer(left: int32, right: int32) {
    requires left < right;
    ensures to_integer(left) < to_integer(right) by auto();
}
```

```expect
pass
```
