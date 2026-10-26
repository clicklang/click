# A claim that cannot lower after `step_until` is refused with its own cause

The proof of
`a_claim_that_cannot_lower_is_refused_ahead_of_a_claim_that_holds.md`,
written as `step_until(function.exit)` instead of omitted. The implicit tail
still closes the claims at exit, and the claim that cannot be lowered is the
refusal, with its lowering error.

```c filename=helper.c
void preserve(int32* pool) {}
int32 run() { int32 pool = 0; preserve(&pool); return 0; }
```

```click
authorized resource ticket(pool: int32*) { field serial: int32; }
verifying "helper.c";
void preserve(int32* pool) {
    owns authority(ticket(pool));
    owns member: ticket(pool);
    ensures member.serial == old(member.serial);
    ensures count(ticket(pool + 1)) >= 0;
} by {
    step_until(function.exit);
}
```

```expect
fail: every pending claim: `ensures to_integer(count(ticket((pool + 1)))) >= 0` failed for `preserve.ensures_1` path 0: could not lower the claim goal
```
