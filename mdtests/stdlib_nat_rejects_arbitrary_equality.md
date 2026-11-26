# stdlib nat rejects arbitrary equality

```click
theorem invalid(a: Nat, b: Nat) {
    ensures a == b by close();
}
```

```expect
fail: invalid.ensures_0
```

