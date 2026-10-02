# Rust slice iterator references

The unchanged `sum.rs` uses `for byte in bytes.iter()` and reads each yielded
shared reference with `*byte`. The contract proves the exact mathematical sum
of arbitrary input bytes at function entry for lengths `0..=1000`, including
empty input, with safe additions and termination.

The exporter checks the resolved standard core slice `.iter()` method and
compiler iterator desugaring. The artifact retains the iterator operation rather
than rewriting it into an index loop. Each successful `next()` saves a shared
address, advances the cursor, and reduces the remaining slice length before the
source body binds `byte`. Dereferencing it requires input views; shared-reference
qualifiers survive local declarations. Rust rejects writing through the
reference. Both reference and copied patterns also work over direct slices.

The state names `__rust_iter_3_5_cursor` and `__rust_iter_3_5_remaining` identify
the loop's source location. No processed-count or index variable is generated.
This sidecar explicitly derives a prefix length from original length minus
remaining length, relates it to the cursor, and bounds each sum by 255 times
that prefix length. Remaining slice length proves termination and obeys the
shared memory model's signed-word length limit. Empty iterators exit without
reading or advancing a pointer.

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
