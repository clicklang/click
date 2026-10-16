# Restricted negated-successor simp exceeds its allocation bound

Soundness: not soundness. Deterministic proof-construction allocation tests
exceed their bounds; these reproductions do not show false acceptance.

Priority: P2.

On unchanged master `471284951`, run:

```sh
cargo nextest run --lib --profile nightly --run-ignored only \
  -E 'test(=surface::proof::proof_object::tests::fixed_state_single_premise_arithmetic_simps_retain_indexed_theorem_steps)'
```

It fails in the restricted negated strict successor case at size 16:

```text
size 16 restricted negated strict successor bound simp allocated 942 persistent nodes (bound 864)
```

The test checks persistent fact-node allocation while constructing fixed-state
and restricted pure proofs, including the exact retained theorem steps and
named premises. The failure is present before any fixture reduction or test
optimization. It does not by itself establish non-linear growth; investigate
the additional allocations rather than assuming a scaling law from one sample.

Acceptance: the named regression passes at every existing size and for every
rule shape, retaining its theorem/premise checks. Preserve logarithmic local
updates and avoid raising the ceiling merely to hide this reproduced failure.

The unchanged sibling regression
`surface::proof::proof_object::tests::predecessor_simps_retain_indexed_named_rule_premises`
also fails at size 16 with:

```text
size 16 restricted click::machine_integer::int32_nonnegative_predecessor_upper_bound allocated 1076 persistent nodes (bound 864)
```

Include that named regression when checking the restricted-proof allocation
fix; it is another existing failing baseline, not an optimization result.
