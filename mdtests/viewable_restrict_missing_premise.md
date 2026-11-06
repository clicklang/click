# Containment alone does not grant viewability

```click
import click::separation;
theorem missing(A: Resource, B: Resource) {
    requires contains(A, B);
    ensures viewable(B) by {
        apply(separation::viewable_restrict(A, B)) using { contains(A, B); };
    }
}
```

```expect
fail: requirement 1 `viewable(A)`
```
