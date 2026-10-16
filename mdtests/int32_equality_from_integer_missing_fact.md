# An order observation is insufficient to identify two machine values

```click
import click::integer;

theorem equality_needs_both_observations(left: int32, right: int32) {
    requires to_integer(left) <= to_integer(right);
    ensures left == right by {
        apply(int32_to_integer_equal_implies_equal(left, right)) using {
            to_integer(left) == to_integer(right);
        };
        assumption();
    }
}
```

```expect
fail: requires an unavailable exact premise: `to_integer(left) == to_integer(right)`
```
