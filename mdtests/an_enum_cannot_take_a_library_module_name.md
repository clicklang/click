# An enum cannot take a Click library module's name

`nat` is an implicit Click library module, so `nat::add` names its `add`.
A file enum `nat` with a constructor `add` would make `nat::add` name both.
Before, the library's function silently won: this theorem verified about
the library's `add`, not the constructor the file declares.

```click
spec enum nat { add(Nat, Nat), other }

theorem t(n: Nat) {
    ensures nat::add(Nat::Zero, n) == n by {
        apply(nat::add_left_identity(n));
    }
}
```

```expect
fail: enum `nat` takes the name of Click library module `click::nat`
```
