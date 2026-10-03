# Rust usize arithmetic

Checked 64-bit `usize` arithmetic, shifts, bitwise assignments, truncating and
sign-extending casts, computed byte-slice indices, and length arithmetic.

Build the pinned Rust exporter with `scripts/build-rust-exporter.sh`, then run:

```sh
cargo run --bin click -- import lock examples/rust-usize/arithmetic.click
cargo run --bin click -- verify examples/rust-usize/arithmetic.click
```
