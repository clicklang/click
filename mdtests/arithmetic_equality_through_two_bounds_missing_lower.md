# A substituted upper bound alone does not establish equality

The two-direction equality planner must refuse when the lower bound is absent.

```click
theorem missing_lower(a: Integer, d: Integer) {
    requires a == d;
    requires d <= 2;
    ensures a == 2 by arithmetic() using { a == d; d <= 2; };
}
```

```expect
fail: no combination of the listed premises proves it
```
