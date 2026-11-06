# Ordinary transport expansion still checks every cited premise

```click
import click::separation;
theorem restrict_view(A: Resource, B: Resource) {
    requires viewable(A);
    requires contains(A, B);
    ensures viewable(B) by {
        transport(viewable(A), viewable(B)) using {
            viewable(A);
            contains(A, B);
            0 == 1;
        };
    }
}
```

```expect
fail: premise
```
