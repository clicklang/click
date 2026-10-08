# `click expand --claim` cannot locate an `exceptional ensures` claim

## Violated invariant

Every claim `click audit` inventories can be expanded by the label the
inventory gives it. `click expand` must find a claim that `click audit` and
`click profile` name.

## Reproduction

```sh
click expand --claim helper.exceptional_ensures_0 \
    mdtests/execute_splits_a_throwing_call_inside_a_c_if.md
```

fails with "could not locate function claim `helper.exceptional_ensures_0`".
The claim is `exceptional ensures exception == 7 by auto;` on `helper`, which
has one smart site. `click audit` reports the claim under that label and then
fails it.

The same failure, found by the whole-repository audit on 2026-10-08:

- `mdtests/execute_splits_a_throwing_call_inside_a_c_if.md`
- `mdtests/grouped_proof_closes_claims_across_two_throwing_calls.md`
- `mdtests/grouped_proof_closes_normal_and_exceptional_claims.md`
- `mdtests/outcomes_routes_a_throw_that_leaves_the_function.md`

each for `helper.exceptional_ensures_0`.

## Effect on the audit

The four files are excluded from the nightly audit in `scripts/check.sh`.
Remove the exclusions with this bug.

## Intended regression

A test beside the whole-claim expansion tests in
`src/surface/tests/expansion_tests.rs` that expands
`helper.exceptional_ensures_0` in the first file and re-verifies the result.

## Acceptance

- `click expand --claim helper.exceptional_ensures_0` succeeds on each of the
  four files and its output verifies.
- `scripts/check.sh --audit` passes without the four exclusions.
