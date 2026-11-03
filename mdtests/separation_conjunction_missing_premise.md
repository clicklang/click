# One separated component does not separate the whole conjunction

```click
import click::separation;
theorem incomplete(A: Resource, B: Resource, C: Resource) {
    requires separate(A, C);
    ensures separate(A * B, C) by {
        apply(separation::separate_star(A, B, C)) using { separate(A, C); };
    }
}
```

```expect
fail: requirement 2 `separate(B, C)`
```
