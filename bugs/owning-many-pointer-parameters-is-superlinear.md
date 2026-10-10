# Exit checks grow faster than linearly in owned pointer parameters

The [efficiency contract](../docs/internals/verification-efficiency.md)
requires explicit simple proofs to verify in work approximately linear in
their source. A function that owns `n` heap objects through `n` pointer
parameters, and writes a cell of one other object, still costs more than
linear work at larger `n`:

```c
struct child {
    int32 refs;
    int32 payload;
};

void touch(struct child* obj, struct child* other0 /* ... */) {
    obj->refs = 1;
}
```

```click
verifying "touch.c";

void touch(struct child* obj, struct child* other0 /* ... */) {
    owns obj->refs;
    owns allocation(other0, sizeof(struct child));
    owns *other0;
    /* ... one pair per parameter ... */
} by {
    step();
    step();
    simp();
}
```

`proof context finishing` costs 6.1k, 13.5k, 35k, 104k, and 349k
deterministic units at `n` = 4, 8, 16, 32, and 64. That is 2.2, 2.6, 3.0, and
3.4 times per doubling. The gate regressions
`owned_pointer_parameters_scale_with_their_number` (3 to 24 parameters) and
`a_retain_ignores_unrelated_live_children` (2 to 16 unrelated children)
pass, but the growth exceeds 3× per doubling beyond 32 parameters.

## Cause

The block-wide scans that dominated are gone. Every pointer parameter
shares the `ExternalArgument` block, and these paths now look up the
queried object's own facts instead:
- `resource_context_contains_exact_owned_fact`;
- `proves_owned_memory_ranges_separate_by`;
- the per-fact recomposition of contract resource contexts.

The remainder is spread across function-exit work done once per contract
clause, with a cost that grows with the number of clauses. The largest
operations are:
- `return resources: definitional check` (3.8× per doubling);
- `ensured resource lowering` (3.9×);
- `execution path preparation` (3.6×);
- `return resource evaluation` (3.2×).

## Regression

Extend both scaling tests to 64 (as nightly tests if they exceed the gate
budget). They fail today.

## Acceptance

- Both scaling tests pass `assert_near_linear_scaling` through 64.
- No other scaling regression gets worse.
