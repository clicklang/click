# Arithmetic derives both directions after an equality substitution

This catches an equality that neither elimination alone nor a direct pair
of the listed premises proves. Each direction needs the substitution and
its own bound; both must be checked before concluding the equality.

```click
theorem equality_through_two_bounds(a: Integer, d: Integer) {
    requires a == d;
    requires d <= 2;
    requires 2 <= d;
    ensures a == 2 by arithmetic() using { a == d; d <= 2; 2 <= d; };
}
```

```expect
pass
```
