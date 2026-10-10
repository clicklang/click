# Owning many pointer parameters costs quadratic or worse work

The [efficiency contract](../docs/internals/verification-efficiency.md)
requires explicit simple proofs to verify in work approximately linear in the
C source, Click source, and certificate. A function that owns `n` separate
heap objects through `n` pointer parameters, and does nothing with most of
them, breaks that rule. Its cost grows faster than `n²`:

```c
struct child {
    int32 refs;
    int32 payload;
};

void touch(struct child* obj, struct child* o0, struct child* o1 /* ... */) {
    obj->refs = 1;
}
```

```click
verifying "p.c";

void touch(struct child* obj, struct child* o0, struct child* o1 /* ... */) {
    owns obj->refs;
    owns allocation(o0, sizeof(struct child));
    owns *o0;
    owns allocation(o1, sizeof(struct child));
    owns *o1;
    /* ... one pair per parameter ... */
} by {
    step();
    step();
    simp();
}
```

Release-build wall time for `click verify`:

| parameters | before batching | after batching (this change) |
| --- | --- | --- |
| 8 | 0.12 s | 0.11 s |
| 16 | 0.30 s | 0.20 s |
| 32 | 1.30 s | 0.54 s |
| 64 | budget exhausted in the final `simp()` | 1.67 s |

The same shape with the shared-heap probe's `child_control`/`child_ref`
resources (one `child_retain` call amid `n` unrelated live children) costs
153k, 286k, 1.18M, and 6.85M deterministic work units at `n` = 4, 8, 16,
and 32. It fails `assert_near_linear_scaling`, and at `n` = 48 it no longer
verifies.

## Cause

Every pointer parameter lives in the one `ExternalArgument` block, because
parameters may alias. Several paths partition by block, so they treat all
`n` parameters' ranges as one bucket:

- `resource_context_contains_exact_owned_fact` (`src/kernel/functions.rs`)
  scans every context fact for each required memory fact, through
  `memory_range_covers`. It is called per control by
  `expand_checked_authority_controls`. In the shared-heap fixture its
  `memory range coverage: fact range` and `fact range coverage: shifted
  base relation` operations dominate (2.8M of 6.85M units at `n` = 32).
- `ResourceContext::validity_error` sweeps every same-block pair, and the
  `ExternalArgument` block holds all of them.
- `call_havoc_keeps_cell` proves each cell separate from the callee's
  footprint through `memory_ranges_proven_disjoint_by_explicit_separation`
  over the same bucket.

Each pairwise check is itself a proof whose cost grows with the fact
context, which compounds the quadratic count.

Two per-fact recompositions were also quadratic. This change batches them:
`evaluate_function_resource_context_with_entry_and_normalization` and
`evaluate_contract_return_resource_context` used to validate and renormalize
the whole context after each fact.

## Regression

Add `a_retain_ignores_unrelated_live_children` to
`src/surface/tests/scaling_tests.rs`. It verifies the shared-heap probe's
`child_retain` once while `n` = 4, 8, 16, 32 unrelated children (each owning
`child_control` and `child_ref`) are live, and asserts
`assert_near_linear_scaling`. Add a plain-ownership companion with the
program above.

## Acceptance

- Both regressions pass `assert_near_linear_scaling` in the normal gate.
- Candidate lookups for a parameter's range use the base-spelling index and
  recorded aliases, not the whole parameter block, and stay complete: a
  range covered through a proven alias or offset relation is still found.
- No other scaling regression gets worse.
