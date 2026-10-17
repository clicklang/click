# Fixed-state predecessor simp exceeds its allocation bound

Soundness: not soundness. An existing proof-construction regression exceeds its
deterministic persistent-node allocation ceiling. This does not demonstrate false
acceptance.

Priority: P2.

On unchanged master `2cee79c02`, run:

```sh
cargo nextest run --lib --profile nightly --run-ignored only \
  -E 'test(=surface::proof::proof_object::tests::fixed_state_predecessor_simp_builds_checked_scope_with_logarithmic_local_updates)'
```

The original size-16 sample fails:

```text
size 16 fixed-state predecessor simp allocated 1368 persistent nodes (bound 1152)
```

The test constructs a checked fixed-state simp descendant and asserts its exact
retained certificate shape, persistent ancestor, and local allocation bound.
Investigate the excess construction allocations; this first-size failure alone
does not establish the asymptotic cause. Preserve the source proof pattern and
all original sample sizes as the regression.

Acceptance: the unchanged test passes at every original size with its retained
proof and persistence assertions. Do not raise the allocation ceiling merely to
hide the failure.
