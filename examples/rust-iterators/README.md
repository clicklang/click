# Rust slice iterator sum

The unchanged `sum.rs` uses `for &byte in bytes` to sum arbitrary input bytes.
Its contract accepts lengths `0..=1000`, including empty input, and proves an
exact mathematical sum of the bytes at function entry. The sidecar chooses a
prefix invariant and bounds each intermediate sum by 255 times that prefix's
length.

Charon retains the standard slice iterator protocol. The checked proof
observations are `iter_cursor` and `iter_remaining`: a successful
`next()` saves the yielded address, advances the cursor, and reduces the remaining
slice length before the source body. The copied pattern reads the saved address.
An exhausted iterator performs no read or pointer advance. Remaining length is
signed under the shared memory model's checked length limit.

No processed count or index is supplied by default. This sidecar explicitly
derives its prefix length as original slice length minus remaining length and
relates it to the cursor. It retains views of the input and uses remaining
length as its decreasing measure.

Immutable shared byte-slice bindings support copied byte patterns and shared
reference variables, directly or through `.iter()`. The
[reference iterator example](../rust-iter-references/README.md) proves a sum
using yielded references. Shared scalar array iteration and stored `.chunks_exact()` iterators also use
actual cursor/remaining state; see the [exact-chunk example](../rust-chunks-exact/README.md).
This fixture covers immutable shared bytes. The pinned checksum libraries remain unverified.

Build the pinned Charon with `scripts/build-charon.sh --install-toolchain`, then run:

```sh
cargo run --bin click -- import lock examples/rust-iterators/sum.click
cargo run --bin click -- verify examples/rust-iterators/sum.click
cargo run --bin click -- profile examples/rust-iterators/sum.click
cargo run --bin click -- audit examples/rust-iterators/sum.click
```

Regression tests reject false results, incorrect invariants, missing bounds,
nondecreasing measures, and unsupported iterator forms. They also verify the
expanded proof through the ordinary CLI.
