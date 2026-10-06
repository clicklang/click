# Explicit mathematical truncation

Quotients truncate toward zero and remainders retain the dividend's sign.
Mathematical division has no native width overflow.

```click
theorem constants() {
    ensures truncating_quotient(-7, 3) == -2 by simp;
    ensures truncating_remainder(-7, 3) == -1 by simp;
    ensures truncating_quotient(7, -3) == -2 by simp;
    ensures truncating_remainder(7, -3) == 1 by simp;
    ensures truncating_quotient(-170141183460469231731687303715884105728, -1) == 170141183460469231731687303715884105728 by simp;
    ensures truncating_remainder(340282366920938463463374607431768211455, 3) == 0 by simp;
}

theorem guarded(a: Integer, b: Integer) {
    requires b != 0;
    ensures truncating_quotient(a, b) == truncating_quotient(a, b) by simp;
    ensures truncating_remainder(a, b) == truncating_remainder(a, b) by simp;
}
```

```expect
pass
```
