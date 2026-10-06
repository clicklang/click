# Swapping Integer equality operands does not change its polarity

```click
theorem equal_arguments(a: Integer, b: Integer) {
    requires a == b;
    ensures a == b by { assumption(); }
}

theorem unequal_arguments(a: Integer, b: Integer) {
    requires b != a;
    ensures a == b by {
        apply(equal_arguments(a, b)) using { b != a; }
    }
}
```

```expect
fail: required exact fact
```
