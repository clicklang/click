# A substituted lower bound alone does not establish equality

The two-direction equality planner must refuse when the upper bound is absent.

```click
theorem missing_upper(a: Integer, d: Integer) {
    requires a == d;
    requires 2 <= d;
    ensures a == 2 by arithmetic() using { a == d; 2 <= d; };
}
```

```expect
fail: no combination of the listed premises proves it
```
