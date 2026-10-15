# a bare nat name needs a path or a selective import

`click::nat` is implicit, but its function `add` is named `nat::add`, or
`add` after `import click::nat::{add};`.

```click
theorem add_zero_by_bare_name(n: Nat) {
    ensures add(Nat::Zero, n) == n by {
        apply(nat::add_left_identity(n));
    }
}
```

```expect
fail: add
```
