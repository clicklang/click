# Rust unsigned conversions and halfword accumulators

`accumulator.rs` uses ordinary `u32::from` calls to widen two `u16` fields
and one byte, then narrows reduced sums back to the fields. Its sidecar
checks the fixed boundary case `a = b = 65520`, `byte = 255`, producing
`a = 254`, `b = 253`. This is a synthetic checksum-style regression; it
does not establish an arbitrary checksum update or verify adler2.

The remaining functions have generic proofs: a shared halfword read preserves
its bytes, an exclusive reference increments without overflow, and a field
update preserves its neighboring field using read authority. Compiler-supplied
layout gives each halfword field its actual two-byte footprint.

Regression tests also cover conversion value preservation, one evaluation in
source order, truncating casts, sixteen-bit shifts and arithmetic, invalid
shift counts, zero divisors, overflow, missing permissions, and false claims.
The fixture's smart proof sites pass expansion audit and checked re-verification.

```sh
scripts/build-charon.sh --install-toolchain
cargo run --bin click -- import lock examples/rust-integer-conversions/accumulator.click
cargo run --bin click -- verify examples/rust-integer-conversions/accumulator.click
cargo run --bin click -- audit examples/rust-integer-conversions/accumulator.click
```
