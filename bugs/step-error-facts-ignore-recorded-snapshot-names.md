# Step-error facts ignore recorded snapshot names

Soundness: sound. Only the wording of a diagnostic is affected; no proof
decision reads these names.

A failure report names a value no current local holds through a recorded
snapshot, `at(iteration, iter_remaining)`
(`register_recorded_snapshot_names` in `src/surface/proof/proof_object.rs`).
Messages a step formats when it fails do not: they spell facts with
`describe_pure_fact_spelled` over `diagnostic_naming_tables()`, which holds
only the current locals and the entry parameters. The same report then names
one value two ways. For example, `assumption`'s refusal in
`src/surface/proof/proof_object/step_application.rs` reads

```text
checked candidate [Rejected]: `sum.contract` proof step tactic 24: `assumption` closes a conjunction when every side is an available fact and a disjunction when one side is; `<unnamed A> - 1u64 < <unnamed A>` is not available
```

while that report's goal line spells the fact
`at(iteration, iter_remaining) - 1u64 < at(iteration, iter_remaining)`.

Reproduce from the repository root: delete the statement
`have iter_remaining < at(iteration, iter_remaining) by { ... }` from a copy of
`examples/rust-iterators/sum.click` (keeping `sum.rs` and the lock files
beside it) and run `click verify --trace-proof sum` on the copy.

Acceptance criteria:

- A fact a step error spells is named the way the report's goal names it,
  including through recorded snapshots, with no per-step cost: the names are
  computed only when the error is rendered.
- The `rust-iterators` regression in `tests/rust_import/iterator_proof.rs`
  extends its `<unnamed` check from the goal line to the whole report.
