# Rust unsigned arithmetic

This synthetic scalar example checks `u8` and `u32` arithmetic through the
shared Click engine. Contracts cover byte accumulation, bounded multiplication,
modular reduction, shift-and-bitwise packing, unsigned comparison, and truncation.
Rust overflow and invalid shift counts are checked obligations; discarding high
bits in a shift and truncating an `as u8` cast are permitted.

Build `scripts/build-charon.sh --install-toolchain`, then run:

```sh
cargo run --bin click -- import lock examples/rust-unsigned/arithmetic.click
cargo run --bin click -- verify examples/rust-unsigned/arithmetic.click
```

This is frontend evidence toward the checksum roadmap. It does not verify an
existing library or support byte slices, loops, or general Cargo projects.
