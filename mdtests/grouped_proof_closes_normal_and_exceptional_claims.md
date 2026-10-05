# A grouped proof closes normal and exceptional claims

The two omitted proofs share one implicit `} by auto;`. On the path where
`helper` throws, the outcome value is the thrown one, which the
`exceptional ensures` clause names `exception`; the grouped `simp` closes
that clause on the throw path and `result == x` on the return path from one
execution. Expanding the grouped proof writes one `outcomes` arm per path.

```c filename=grouped_proof_closes_normal_and_exceptional_claims.c
int32 helper(int32 x) { return x; }
int32 caller(int32 x) { return helper(x); }
```

```click
verifying "grouped_proof_closes_normal_and_exceptional_claims.c";

int32 helper(int32 x) throws int32 {
    ensures result == x by auto;
    exceptional ensures exception == 7 by auto;
}

int32 caller(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}
```

```expect
pass
```
