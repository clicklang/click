# The implicit grouped proof reports its failing claim

The two omitted proofs share one implicit `} by auto;`, so a false claim
fails inside that grouped proof, which still names the claim it could not
close.

```c filename=implicit_grouped_proof_reports_the_failing_claim.c
int32 inc(int32 x) {
    return x + 1;
}
```

```click
verifying "implicit_grouped_proof_reports_the_failing_claim.c";

int32 inc(int32 x) {
    requires x >= 0 and x <= 100;
    ensures result >= 1;
    ensures result <= 50;
}
```

```expect
fail: did not retain a complete proof for `inc.ensures_1`
```
