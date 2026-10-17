# Adler's false full-batch B invariant exhausts the smart budget

Soundness: incomplete. The false invariant is rejected, but by exhausting the
smart budget instead of producing the bounded proof refusal required by the
existing negative control. No false claim is known to be accepted.

Reproduces on `2cee79c02` with the unchanged pinned Rust import and source:

```sh
cargo nextest run --test rust_import --profile nightly --run-ignored all \
  -E 'test(=adler2_helpers::charon_adler2_general_compute_rejects_false_b_specification)'
```

The test in `tests/rust_import/adler2_helpers.rs` mutates
`design/charon-trial/adler2/general-compute.click`. Its first mutation changes
the outer loop's B-specification seed from `old(to_integer((self.b as u32)))`
to that seed plus one. `reject_compute` checks the selected compute body and
requires a proof error that is not budget exhaustion.

Instead, loop 0 invariant 37 entry exhausts `plan_invariant_entry` after
2,000,001 work units against the existing 2,000,000-unit limit, at statement
523. The reported obligation contains a long chain of implications from the
entry conditions to the mutated invariant. The local named test fails in
about 19 seconds; this is a work-budget failure, not a wall-clock timeout.

The violated invariant is bounded refusal of this existing false-specification
control. Investigate the entry planner's selected evidence and failed search;
the exact cause has not yet been reduced. The scalar-tail stale-A control was
repaired separately by proving its assignment chain explicitly. This invariant-entry search still needs its own
investigation.

Acceptance: the named test rejects both of its existing mutations with proof
errors below the unchanged work limit. Preserve the Rust source, the valid
contract, and the mutations. The original general compute proof and its
expanded certificates must still verify. Do not raise budgets or allow budget
exhaustion as an expected refusal.
