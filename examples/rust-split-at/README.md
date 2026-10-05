# Shared Rust slice splitting

`split.rs` uses the standard `split_at` method on unchanged shared byte-slice
functions. The sidecar proves the lengths of both results and the original
byte values read through each result, for variable split points. The split
copies metadata only; reads retain the original input's byte views.

The compiler-resolved `SliceSplit` operation evaluates the receiver before the
midpoint, evaluates the midpoint once, and checks `mid <= bytes_len` at full
`usize` width. Pointer formation additionally requires `mid <= INT32_MAX` in
the current memory model. Lengths remain 64-bit. Endpoint and empty splits
are legal; an indexed read still requires a nonempty result.

This increment supports two plain tuple bindings from a local `&[u8]`.
General tuples, discarded tuple elements, direct array receivers, mutable
receivers, and `split_at_mut` remain outside the subset. It does not verify
the pinned checksum libraries.

Build the pinned Charon with `scripts/build-charon.sh --install-toolchain`, then run:

```sh
cargo run --bin click -- import lock examples/rust-split-at/split.click
cargo run --bin click -- verify examples/rust-split-at/split.click
cargo run --bin click -- profile examples/rust-split-at/split.click
cargo run --bin click -- audit examples/rust-split-at/split.click
```
