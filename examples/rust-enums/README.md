# Rust enums and match

A crate enum with tuple, struct and fieldless variants is the sidecar's
`spec enum Shape`. Contracts cover construction, a `match` whose requirements
bound each variant's fields, a `+ 1` whose panic check uses the requirement
instantiated in the `Circle` arm, `matches!`, `if let` proved with a written
proof `match`, and an integer `match` with an or-pattern and a wildcard.
`execute()` splits each open enum `match` with a proof `match`.

Build `scripts/build-charon.sh --install-toolchain`, then run:

```sh
cargo run --bin click -- import lock examples/rust-enums/shapes.click
cargo run --bin click -- verify examples/rust-enums/shapes.click
```

Generic enums, `Option<T>`, references to enums, and enums inside structs are
not supported yet.
