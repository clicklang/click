# Adler's stale scalar A control exhausts the smart budget

Soundness: incomplete. A false scalar-tail equality is rejected through budget
exhaustion instead of the bounded semantic refusal required by the existing
negative control. No false claim is known to be accepted.

Reproduces on `2cee79c02` with the unchanged pinned Rust import and source:

```sh
cargo nextest run --test rust_import --profile nightly --run-ignored all \
  -E 'test(=adler2_helpers::charon_adler2_small_batch_compute_rejects_stale_scalar_a)'
```

The test in `tests/rust_import/adler2_helpers.rs` changes one `have` in
`design/charon-trial/adler2/small-batch-compute.click`, removing the added byte
from the equality:

```click
have to_integer(at(tail_add_b, __rust_mir_147)) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, __rust_mir_144));
```

The mutated equality falsely omits the newly added byte. `reject_compute`
requires its rejection without budget exhaustion. Instead, compute tactic
676 (`loop`), preserve tactic 87 exhausts the `have` search after 2,000,001
work units against the existing 2,000,000-unit limit (statement 1689, source
tactic 1000). The local named test fails in about 56 seconds; this is a
work-budget failure, not a wall-clock timeout.

The violated invariant is bounded refusal of this existing stale-value
control. Reduce the failed equality's proof search and snapshot evidence;
its exact cause is not established. The full-batch invariant-entry control
fails separately, as recorded in
[adler-general-false-b-invariant-exhausts-smart-budget.md](adler-general-false-b-invariant-exhausts-smart-budget.md).

Acceptance: the original mutation fails with a proof error below the unchanged
work limit, while the unmutated small-batch computation and its expanded
certificates still verify. Preserve the native Rust, contracts, and mutation;
do not raise limits or accept budget exhaustion as the negative verdict.
