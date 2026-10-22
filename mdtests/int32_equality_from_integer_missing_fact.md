# An order observation is insufficient to identify two machine values

```click
import click::integer;

theorem equality_needs_both_observations(left: int32, right: int32) {
    requires to_integer(left) <= to_integer(right);
    ensures left == right by auto();
}
```

```expect
fail: could not establish `left == right`
```
