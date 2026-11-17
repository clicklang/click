# `normalize` cancels two copies of one fold

Each occurrence of a fold in a proposition is lowered with its own binders, so
the two sides of `F == F - 0` hold different but alpha-equivalent fold terms.
Integer normalization treats a fold as an opaque atom keyed by its checked
alpha identity, so the copies cancel exactly as two copies of `n` would.

```c filename=normalize_cancels_separately_lowered_copies_of_a_fold.c
int32 f(int32 n) {
    return n;
}
```

```click
verifying "normalize_cancels_separately_lowered_copies_of_a_fold.c";

int32 f(int32 n) {
    requires 0 <= n and n <= 10;
    ensures result == n;
} by {
    have (0..n).fold(0, |acc, k| { (acc + to_integer(k)) }) ==
        ((0..n).fold(0, |acc, k| { (acc + to_integer(k)) }) - 0) by {
        normalize();
    }
    have -(0..n).fold(0, |acc, k| { (acc + to_integer(k)) }) ==
        (0 - (0..n).fold(0, |acc, k| { (acc + to_integer(k)) })) by {
        normalize();
    }
    step_until(function.exit);
}
```

```expect
pass
```
