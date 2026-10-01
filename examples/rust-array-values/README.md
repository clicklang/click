# Rust local array values

This synthetic example verifies literal and repeat constructors for scalar
fixed arrays, independent copies, whole-array assignment through references,
local borrows, and empty arrays. Calls in constructors check source evaluation
order and that repeats evaluate their operand once, including zero repeats.
The copy contracts require authority over every source and destination element.

```sh
scripts/build-rust-exporter.sh
cargo run --bin click -- import lock examples/rust-array-values/arrays.click
cargo run --bin click -- verify examples/rust-array-values/arrays.click
cargo run --bin click -- audit examples/rust-array-values/arrays.click
```
