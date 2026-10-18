# `simp` after execution acts on the first open claim

After execution `simp()` closes the first open goal, as the other closers do;
`auto` is the catch-all that closes every goal still open. Here `simp()`
closes `result == 1` and leaves `result == n` for `normalize()`. When `simp`
closed every claim it could, `normalize()` was refused for having no goal.

```c filename=simp_after_execution_acts_on_the_first_open_claim.c
int32 f(int32 n) {
    return n;
}
```

```click
verifying "simp_after_execution_acts_on_the_first_open_claim.c";

int32 f(int32 n) {
    requires n == 1;
    ensures result == 1;
    ensures result == n;
} by {
    execute();
    simp();
    normalize();
}
```

```expect
pass
```
