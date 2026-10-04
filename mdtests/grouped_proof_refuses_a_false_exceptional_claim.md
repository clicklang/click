# A grouped proof refuses a false exceptional claim

The negative of
`mdtests/grouped_proof_closes_normal_and_exceptional_claims.md`: `helper`
throws 7, so the caller's claim that it throws 8 fails on the throw path.

```c filename=grouped_proof_refuses_a_false_exceptional_claim.c
int32 helper(int32 x) { return x; }
int32 caller(int32 x) { return helper(x); }
```

```click
verifying "grouped_proof_refuses_a_false_exceptional_claim.c";

int32 helper(int32 x) throws int32 {
    ensures result == x by auto;
    exceptional ensures exception == 7 by auto;
}

int32 caller(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 8;
}
```

```expect
fail: did not retain a complete proof for `caller.exceptional_ensures_0`
```
