# Rust slice iterator references

The unchanged `sum.rs` uses `for byte in bytes.iter()` and reads each yielded
shared reference with `*byte`. The contract proves the exact mathematical sum
of arbitrary input bytes at function entry for lengths `0..=1000`, including
empty input, with safe additions and termination.

The Charon adapter checks the resolved standard core slice `.iter()` method and
compiler iterator desugaring. The artifact retains the iterator operation rather
than rewriting it into an index loop. Each successful `next()` saves a shared
address, advances the cursor, and reduces the remaining slice length before the
source body binds `byte`. Dereferencing it requires input views; shared-reference
qualifiers survive local declarations. Rust rejects writing through the
reference. Both reference and copied patterns also work over direct slices.

The proof observes `iter_cursor` and `iter_remaining`, without MIR IDs or a
generated processed count. It derives a prefix length from original length
minus remaining length, relates it to the cursor, and bounds each sum by 255
times that prefix length. `let loaded_byte = step();` names the actual checked
scalar read, retaining its value after compiler temporaries leave scope.
Remaining slice length proves termination and obeys the shared memory model's
signed-word length limit. Empty iterators exit without reading or advancing a
pointer.

Shared scalar array iteration and stored `.chunks_exact()` iterators also use
actual cursor/remaining state; see the [exact-chunk example](../rust-chunks-exact/README.md).
This fixture covers immutable shared bytes. The pinned checksum libraries remain unverified.

Build the pinned Charon with `scripts/build-charon.sh --install-toolchain`, then run:

```sh
cargo run --bin click -- import lock examples/rust-iter-references/sum.click
cargo run --bin click -- verify examples/rust-iter-references/sum.click
cargo run --bin click -- profile examples/rust-iter-references/sum.click
cargo run --bin click -- audit examples/rust-iter-references/sum.click
```

Regression tests reject false results, missing length bounds, missing views,
nondecreasing measures, unsupported iterators, and writes through shared
references. They also verify the expanded proof through the ordinary CLI.
