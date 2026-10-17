# Restricted symbolic-add simp exceeds its allocation bound

Soundness: not soundness. An existing deterministic proof-construction allocation
regression exceeds its ceiling; this reproduction does not show false acceptance.

Priority: P2.

On unchanged master `bf7d77d91`, run:

```sh
cargo nextest run --lib --profile nightly --run-ignored only \
  -E 'test(=surface::proof::proof_object::tests::symbolic_arithmetic_definedness_retains_two_indexed_theorem_premises)'
```

The restricted symbolic-add case fails at its first size:

```text
size 16 restricted symbolic-add simp allocated 1253 persistent nodes (bound 864)
```

The regression checks fixed-state and restricted pure arithmetic rule applications,
including exact retained theorem names and both selected premises. The failure was
reproduced before changing any test fixture. This one sample does not establish a
scaling law; investigate the extra allocations in restricted proof construction.

Acceptance: the existing test passes for every rule and every original size,
retaining its theorem, premise, persistence, and allocation checks. Preserve local
updates and do not raise the ceiling merely to hide the failure.
