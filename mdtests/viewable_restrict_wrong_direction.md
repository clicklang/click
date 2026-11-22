# Viewability does not extend to a containing resource

```click
import click::separation;
theorem backwards(A: Resource, B: Resource) {
    requires viewable(A);
    requires contains(B, A);
    ensures viewable(B) by {
        apply(separation::viewable_restrict(A, B));
    }
}
```

```expect
fail: has an unproved obligation: `contains(A, B)`
```
