# Exact signed 64-bit operations observed as Integers

Definedness is required before native addition or subtraction can be observed
as the corresponding mathematical operation. No overflow fact is inferred.

```click
import click::integer;

theorem exact64_sum(left: int64, right: int64) {
    requires defined(left + right);
    ensures to_integer(left + right) == to_integer(left) + to_integer(right);
}
theorem exact64_difference(left: int64, right: int64) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right);
}
```

```expect
pass
```
