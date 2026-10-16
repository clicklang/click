# an Integer premise files no stronger machine fact

The native fact filed beside `to_integer(x) < 10` is `x < 10`, not more:
it does not bound `x` below.

```click
theorem integer_upper_bound_is_not_a_lower_bound(x: int32) {
    requires to_integer(x) < 10;
    ensures 0 <= x by auto;
}
```

```expect
fail: 0 <= x
```
