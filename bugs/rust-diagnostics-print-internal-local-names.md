# Rust proof diagnostics print internal local names

Soundness: sound. This is a diagnostic defect: the verdict is unaffected, but
reports name values by translation temporaries no source or proof can cite.

A failure report for an imported Rust function spells some values through
the C locals the Rust lowering introduced instead of their source spelling.
In the `rust-iterators` sidecar (`examples/rust-iterators/sum.click`), a
back-edge closure failure prints

```text
goal: to_integer(at(statement(93).exit, total) + __rust_mir_11) == prefix(old(__rust_checked_2), __rust_checked_3, __rust_checked_3 - (at(iteration, iter_remaining) - 1u64)) ...
```

`__rust_checked_2` and `__rust_checked_3` are the slice parameter's pointer
and length, which the proof writes `bytes` and `bytes.len()`, and
`__rust_mir_11` is the copied loop binding the proof writes `byte`. The same
report's "pure facts" list already spells them as `bytes` and `bytes.len()`,
so the two renderers disagree.

Reproduce from the repository root: delete the statement
`have iter_remaining < at(iteration, iter_remaining) by { ... }` from a copy of
`examples/rust-iterators/sum.click` (keeping `sum.rs` and the lock files
beside it) and run `click verify` on the copy.

The `__click` filter in `register_snapshot_names`
(`src/surface/proof/proof_object.rs`) does not cover the `__rust_` temporaries,
and the current-state naming registers them as source names.

Acceptance criteria:

- The reproduction's report spells the slice as `bytes`, its length as
  `bytes.len()`, and the copied byte as `byte` (or another spelling a proof
  can write), and contains no `__rust_` name.
- A regression in `tests/rust_import/iterator_proof.rs` asserts that
  `rust-iterators` failure reports contain no `__rust_` name.
