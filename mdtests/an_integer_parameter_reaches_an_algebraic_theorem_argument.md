# An Integer parameter reaches an algebraic theorem argument

`uses_integer` applies `nat_image` to `to_nat(z - 1)`, an algebraic argument
built from its own `Integer` parameter `z`. The argument is read with the
caller's `Integer` bindings, as an `Integer` argument is, so `z` is known
while the callee's precondition is instantiated.

```click
theorem nat_image(n: Nat) {
    requires to_integer(n) >= 0;
    ensures to_integer(n) >= 0;
}

theorem uses_integer(z: Integer) {
    requires z > 0;
    ensures to_integer(to_nat(z - 1)) >= 0 by {
        apply(nat::to_integer_to_nat(z - 1));
        apply(nat_image(to_nat(z - 1)));
    }
}
```

```expect
pass
```
