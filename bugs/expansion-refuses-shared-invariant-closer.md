# Expansion refuses an invariant closer checked across different obligations

## Violated invariant

A smart tactic that verifies must expand to explicit tactics that verify the
same claim. A shared loop-invariant closer can produce different certificates
for its individual obligations, but capture requires identical expansions and
refuses the rewrite.

This is the remaining independent reproduction from the former combined
path-dependent-expansion report. The C++ guard audit already passes. The
bubble-sort permutation claim closer instead needed its proofs placed in the
original execution leaves, with terminal routing retaining each exact branch
decision. The sorted fixture's post-execution `have` rewrite is tracked separately.

## Reproduction

On `master` at `4bc08bee6`, ordinary verification passes, but:

```sh
click audit mdtests/c_decreases_recursive_in_loop.md
```

fails at line 53 (`close_invariants`) with:

```text
selected tactic expands differently across proof obligations
```

Three preceding sites pass; the audit discovers five sites in this claim.
Keep the fixture's C and contract unchanged.

## Intended regression

Retain a small shared invariant closer with multiple obligations whose checked
certificates differ. Expand the closer and independently verify its rewrite.
Use the bounded shared engine, rather than adding a whole-fixture CLI audit to
the regular gate.

## Acceptance criteria

- Every site in `mdtests/c_decreases_recursive_in_loop.md` audits successfully.
- The shared closer expands to explicit checked proofs for all its obligations.
- The fix is generic capture/checker work; `scripts/check.sh` passes.
