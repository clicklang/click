# A grouped proof that proves no claim is refused

The negative of `mdtests/grouped_proof_covers_claims_without_their_own.md`:
every postcondition has its own `by`, so the grouped proof would prove
nothing and is refused rather than silently unused.

```c filename=grouped_proof_that_proves_no_claim_is_refused.c
int32 inc(int32 x) {
    return x + 1;
}
```

```click
verifying "grouped_proof_that_proves_no_claim_is_refused.c";

int32 inc(int32 x) {
    requires x >= 0 and x <= 100;
    ensures result >= 1 by auto;
    ensures result <= 101 by auto;
} by auto;
```

```expect
fail: this grouped function proof proves no claim
```
