# Viewability restriction requires containment

```click
import click::separation;
theorem restrict_view(A: Resource, B: Resource) {
    requires viewable(A);
    ensures viewable(B) by {
        apply(separation::viewable_restrict(A, B));
    }
}
```

```expect
fail: theorem `click::separation::viewable_restrict` has an unproved obligation
```
