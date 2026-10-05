# Nested Rust guards

This synthetic example keeps ordinary safe Rust source. The second guard
borrows the first guard's saved field. Its destructor writes 42 to that field;
the first guard's destructor then writes 42 to the caller's integer.

Click checks both destructor applications with ordinary `owns` contracts.
The returned field owner and the retained storage fragments jointly supply
the outer destructor's memory requirement. Every fragment is consumed once;
a view or missing fragment cannot supply ownership. No new sidecar syntax is
needed. rustc establishes the source borrows' legality; Click checks the
extracted memory operations and functional claims.

Build `scripts/build-charon.sh --install-toolchain`, then run:

```sh
cargo run --bin click -- import lock examples/rust-field-borrow/guard.click
cargo run --bin click -- verify examples/rust-field-borrow/guard.click
```
