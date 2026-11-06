# Viewability does not extend to a containing resource

```click
import click::separation;
theorem backwards(A: Resource, B: Resource) {
    requires viewable(A);
    requires contains(B, A);
    ensures viewable(B) by {
        apply(separation::viewable_restrict(A, B)) using {
            viewable(A);
            contains(B, A);
        };
    }
}
```

```expect
fail: requirement 2 `contains(A, B)`
```
