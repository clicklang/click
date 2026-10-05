# A grouped proof closes claims across two throwing calls

`caller` steps over two maybe-throwing calls, and its normal path continues
after the first. The omitted proofs share one implicit `} by auto;`, which
closes `result == x` on the returned path and `exception == 7` on each
throw path. Expanding it writes an `outcomes` at each call: the first call's
`returned` arm continues to the second call, whose `outcomes` sits inside it.
`mdtests/outcomes_routes_a_throw_that_leaves_the_function.md` writes that
form by hand.

```c filename=grouped_proof_closes_claims_across_two_throwing_calls.c
int32 helper(int32 x) { return x; }
int32 caller(int32 x) {
    int32 y = helper(x);
    int32 z = helper(y);
    return z;
}
```

```click
verifying "grouped_proof_closes_claims_across_two_throwing_calls.c";

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
