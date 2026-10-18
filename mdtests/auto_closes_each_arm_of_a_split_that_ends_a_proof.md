# `auto` closes each arm of a split that ends a proof

A proof `if` after execution whose condition is open on the outcome path splits
that path in two, and each arm finishes its own path. `auto();` written at the
end of an arm closes that arm's goals: here `simp()` closes the first claim in
each arm and `auto()` the rest.

```c filename=auto_closes_each_arm_of_a_split_that_ends_a_proof.c
int32 f(int32 n) {
    return n;
}
```

```click
verifying "auto_closes_each_arm_of_a_split_that_ends_a_proof.c";

int32 f(int32 n) {
    ensures result == n;
    ensures n < 5 or n >= 5;
    ensures n == n;
} by {
    execute();
    if n < 5 {
        simp();
        auto();
    } else {
        simp();
        auto();
    }
}
```

```expect
pass
```
