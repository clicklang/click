# Closers after execution close a resource goal first

The companion of `a_resource_claim_is_a_goal_in_contract_order.md`.
`assumption()` closes the first goal, `owns p[0..1]`, because the path holds
the cell, and `normalize()` then closes `result == 7`.

```c filename=closers_after_execution_close_a_resource_goal_first.c
int32 g(int32 p[]) {
    return 7;
}
```

```click
verifying "closers_after_execution_close_a_resource_goal_first.c";

int32 g(int32 p[]) {
    owns p[0..1];
    ensures result == 7;
} by {
    execute();
    assumption();
    normalize();
}
```

```expect
pass
```
