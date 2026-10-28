# Rust `bool` values

A Rust `bool` is Click's `Bool`. A comparison, `!`, `&&` or `||` that
produces a `bool` value is the condition it tests, with no path split, so
`let c = a < b;`, `!b` in a `match` arm and `a != b` over `bool`s verify
without a written case split. A `bool` field of a crate enum and the payload
of an `Option<bool>` are `Bool` values too.

Build `scripts/build-charon.sh --install-toolchain`, then run:

```sh
cargo run --bin click -- import lock examples/rust-bools
cargo run --bin click -- verify examples/rust-bools/bools.click
```

`&bool` parameters and slices of `bool` are not supported yet.
