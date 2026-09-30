# First Rust verification example

`borrow.rs` is unchanged Rust source. `borrow.click` proves a scalar branch,
parent reuse after a mutable reborrow, a direct field helper call with a frame
for the other field, and a shared-field borrow across a disjoint write.

Install the pinned exporter toolchain once:

```sh
scripts/setup-environment.sh
scripts/build-rust-exporter.sh
cargo run --bin click -- import lock examples/basic-rust/borrow.click
cargo run --bin click -- verify examples/basic-rust/borrow.click
```

Run commands from the repository root. Generated artifacts and locks are local
outputs. Ordinary verification loads them without running rustc. See the
[experimental Rust reference](../../docs/reference/rust.md) for supported
semantics and the compiler/translator trust boundary.
