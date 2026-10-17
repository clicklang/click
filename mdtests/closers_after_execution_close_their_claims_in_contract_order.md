# Closers after execution close their claims in contract order

The companion of `a_closer_after_execution_acts_on_the_first_open_claim.md`.
Written in contract order, `normalize()` closes `2 + 2 == 4` and `assumption()`
then closes `result == n`.

```c filename=closers_after_execution_close_their_claims_in_contract_order.c
int32 f(int32 n) {
    return n;
}
```

```click
verifying "closers_after_execution_close_their_claims_in_contract_order.c";

int32 f(int32 n) {
    ensures 2 + 2 == 4;
    ensures result == n;
} by {
    execute();
    normalize();
    assumption();
}
```

```expect
pass
```
