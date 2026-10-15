# a selective nat import brings bare names

```click
import click::nat::{add, add_left_identity};

theorem add_zero_by_bare_names(n: Nat) {
    ensures add(Nat::Zero, n) == n by {
        apply(add_left_identity(n));
    }
}
```

```expect
pass
```
