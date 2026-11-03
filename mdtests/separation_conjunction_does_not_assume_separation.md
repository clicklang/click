# Naming a conjunction does not supply its operands' separation or ownership

```click
import click::separation;
theorem no_permission(A: Resource, B: Resource) {
    ensures separate(A, B) by {
        apply(separation::contains_left(A, B)) using {};
        apply(separation::contains_right(A, B)) using {};
        assumption();
    }
}
```

```expect
fail: `assumption` requires the current goal as an available semantic fact
```
