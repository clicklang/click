# Arithmetic certificate syntax has been removed

Arithmetic search expands to ordinary proof steps. The old public certificate
syntax is no longer a proof tactic.

```click
theorem removed(x: Integer) {
    ensures x == x by {
        arithmetic_certificate { trivial => x == x; conclusion 0; }
    }
}
```

```expect
fail: arithmetic_certificate
```
