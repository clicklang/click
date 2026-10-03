# Rust array-to-slice coercions

This synthetic example passes fixed byte arrays and array references to
shared and mutable byte-slice helpers. It verifies local slice aliases,
reassignment to arrays of different lengths, parent reuse after helper calls,
and empty-array lengths. Coercions retain the original storage and do not grant
memory authority; helper contracts require only the elements they access.

```sh
scripts/build-rust-exporter.sh
cargo run --bin click -- import lock examples/rust-array-slices/arrays.click
cargo run --bin click -- verify examples/rust-array-slices/arrays.click
cargo run --bin click -- audit examples/rust-array-slices/arrays.click
```
