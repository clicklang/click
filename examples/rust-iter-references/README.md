# Rust slice iterator references

The unchanged `sum.rs` uses `for byte in bytes.iter()` and reads each yielded
shared reference with `*byte`. The contract proves the exact mathematical sum
of arbitrary input bytes at function entry for lengths `0..=1000`, including
empty input, with safe additions and termination.

The exporter checks the resolved standard core slice `.iter()` method and
compiler iterator desugaring. Each binding is a shared `&u8` address computed
with full-width bounds checks. Dereferencing it requires the input views;
shared-reference qualifiers survive local declarations. Rust rejects writing
through the reference. Both reference and copied byte patterns also work when
iterating the slice directly.

The native `usize` progress counter `__rust_iter_index_3_5` names this loop's
source location. Prefix invariants and `0 <= total <= 255 * counter` connect
progress to the mathematical sum and bound each intermediate result. The
measure `bytes_len - counter` proves termination.

Only immutable shared byte-slice bindings are supported. Mutable iteration,
array iteration, stored iterator locals, `.chunks_exact()`, custom iterators,
labels, `break`, and `continue` remain unsupported. The pinned checksum
libraries remain unverified.

Build the pinned exporter with `scripts/build-rust-exporter.sh`, then run:

```sh
cargo run --bin click -- import lock examples/rust-iter-references/sum.click
cargo run --bin click -- verify examples/rust-iter-references/sum.click
cargo run --bin click -- profile examples/rust-iter-references/sum.click
cargo run --bin click -- audit examples/rust-iter-references/sum.click
```

Regression tests reject false results, missing length bounds, missing views,
nondecreasing measures, unsupported iterators, and writes through shared
references. They also verify the expanded proof through the ordinary CLI.
