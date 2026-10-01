# Rust slice iterator sum

The unchanged `sum.rs` uses `for &byte in bytes` to sum arbitrary input bytes.
Its contract accepts lengths `0..=1000`, including empty input, and proves an
exact mathematical sum of the bytes at function entry. Prefix invariants and
`0 <= total <= 255 * counter` prove the result and every signed addition safe.

The compiler exporter recognizes the resolved standard slice iterator
protocol and copies each yielded byte through checked indexing. It exposes
`__rust_iter_index_3_5`, a native `usize` counter named for this loop's source
location, for invariants and the decreasing measure `bytes_len - counter`.
The sidecar retains views of the input and checked full-width index bounds.

Immutable shared byte-slice bindings support copied byte patterns and shared
reference variables, directly or through `.iter()`. The
[reference iterator example](../rust-iter-references/README.md) proves a sum
using yielded references. Mutable slices/bindings, array iteration, stored
iterator locals, `.chunks_exact()`, labels, `break`, and `continue` remain
unsupported. The pinned checksum libraries remain unverified.

Build the pinned exporter with `scripts/build-rust-exporter.sh`, then run:

```sh
cargo run --bin click -- import lock examples/rust-iterators/sum.click
cargo run --bin click -- verify examples/rust-iterators/sum.click
cargo run --bin click -- profile examples/rust-iterators/sum.click
cargo run --bin click -- audit examples/rust-iterators/sum.click
```

Regression tests reject false results, incorrect invariants, missing bounds,
nondecreasing measures, and unsupported iterator forms. They also verify the
expanded proof through the ordinary CLI.
