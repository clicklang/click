# Rust while loops

Synthetic regressions for checked scalar accumulation and byte-slice iteration
with ordinary Click loop invariants and decreasing measures. The slice counter
uses the full 64-bit `usize` width. The accumulator's contract fixes its input
value to one; this example does not prove a checksum implementation.

Build the pinned exporter with `scripts/build-rust-exporter.sh`, then run:

```sh
cargo run --bin click -- import lock examples/rust-loops/loops.click
cargo run --bin click -- verify examples/rust-loops/loops.click
cargo run --bin click -- audit examples/rust-loops/loops.click
```
