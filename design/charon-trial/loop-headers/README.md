# Split while headers

`loops.rs`/`loops.click` and `sum.rs`/`sum.click` are byte-for-byte copies of
`rust-loops` and `rust-byte-sum`. Both now import through Charon. The frozen
sidecars retain their numeric-frontier failures: respectively “requires the
execution frontier to be at a loop” and “local `i` has no value at this frontier”.
They remain proof gaps in the parity inventory.

`loops-proof.click` changes only three entry selectors to `loop(0)`. Its three
contracts verify the unchanged count, accumulate, and byte-walk bodies.
`headers.rs` additionally proves an assignment performed on the final false
header test and a negated shared-slice-length comparison. False result claims
fail; verification, profiling, auditing, and expanded certificates agree.
These adapted/synthetic proofs do not increase frozen fixture parity.

The adapter recognizes a linear, single-entry chain from the natural header to
its conditional test. It reconstructs the guard in statement order using
bounded pure scalar substitution and shared-slice metadata, then emits the
original header statements on every test, including the final false test.
It preserves actual local state and emits no processed-count variable or
manufactured break. Single-block headers retain their existing structure.

Guard substitution is limited to 256 expression nodes. Ordinary calls, memory
reads, arithmetic, mutable/reference borrows, shared header entries, and extra
exits remain rejected. Scaling regressions at 8, 32, and 128 header blocks check
linear charged work and emitted statement counts; nested-loop regressions
remain covered. Live extraction also checks these rejected source shapes and
retains the complete frozen parity sweep.

`split-shared-slice-while-header-v1` versions this semantic expansion. Previous
ULLBC artifacts, compiler pins, and extraction flags are unchanged; locks are
updated deliberately. External Charon locks require an explicit refresh.

```sh
scripts/check.sh --charon-live
cargo nextest run --lib --test rust_import -E 'test(charon_loop_headers_) | test(split_while_) | test(mir_while_) | test(nested_while_)'
```

Current fixture parity is 10/16 (62.5%); import coverage is 14/16 (87.5%). Next
resolve stable proof observations for numeric frontiers and iterator state,
plus the remaining owned-iterator and tuple/slice-return normalization gaps,
before switching the default and retiring legacy extraction.
