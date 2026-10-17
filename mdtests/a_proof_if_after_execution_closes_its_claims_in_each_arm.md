# A proof `if` after execution closes its claims in each arm

The companion of `a_proof_if_after_execution_that_would_fork_is_refused.md`.
With the closing `simp()` written inside the arms, nothing follows the `if`,
and each arm closes the claims on its own path.

```c filename=a_proof_if_after_execution_closes_its_claims_in_each_arm.c
int32 f(int32 n) {
    return n;
}
```

```click
verifying "a_proof_if_after_execution_closes_its_claims_in_each_arm.c";

int32 f(int32 n) {
    requires 0 <= n;
    requires n <= 10;
    ensures result <= 10;
    ensures result >= 0;
} by {
    execute();
    if n < 5 {
        have n <= 10 by assumption();
        simp();
    } else {
        have n <= 10 by assumption();
        simp();
    }
}
```

```expect
pass
```
