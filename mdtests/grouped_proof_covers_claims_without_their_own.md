# A grouped proof covers the claims without their own proof

A claim with its own `by` keeps that proof, and the function's grouped proof
proves every other claim from one shared execution. When two or more claims
omit their proofs and no grouped proof is written, they share an implicit
`} by auto;`: `omitted` executes `inc` once, not once per claim.

```c filename=grouped_proof_covers_claims_without_their_own.c
int32 inc(int32 x) {
    return x + 1;
}

int32 omitted(int32 x) {
    return x + 1;
}

int32 mixed(int32 x) {
    return x + 1;
}
```

```click
verifying "grouped_proof_covers_claims_without_their_own.c";

int32 inc(int32 x) {
    requires x >= 0 and x <= 100;
    ensures result >= 1 by {
        execute();
        simp();
    }
    ensures result <= 101;
    ensures result != 0;
} by auto;

int32 omitted(int32 x) {
    requires x >= 0 and x <= 100;
    ensures result >= 1;
    ensures result <= 101;
}

int32 mixed(int32 x) {
    requires x >= 0 and x <= 100;
    ensures result >= 1 by auto;
    ensures result <= 101;
    ensures result <= 200;
}
```

```expect
pass
```
