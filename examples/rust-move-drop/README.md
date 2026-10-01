# Rust move/drop guard

`guard.rs` stays ordinary safe Rust. A guard saves a borrowed integer, moves
into another local, and restores the integer through its `Drop` implementation.
Both the normal and early return capture the current integer before cleanup.

`guard.click` checks the destructor's effect and proves that `restore` returns
7 or 9 while restoring the caller's original integer. The compiler exports
actual cleanup edges; Click verifies the destructor contract and checked
whole-value liveness transitions.

Build the pinned exporter with `scripts/build-rust-exporter.sh`, then run:

```sh
cargo run --bin click -- import lock examples/rust-move-drop/guard.click
cargo run --bin click -- verify examples/rust-move-drop/guard.click
```

See [the Rust reference](../../docs/reference/rust.md) for the supported subset.
Integration regressions also cover conditional moves, explicit `drop`, reverse
cleanup order, and rejected duplicate moves, duplicate drops, and missing cleanup.
