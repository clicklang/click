# Fixed-array references

This synthetic Rust fixture checks references to fixed arrays of `u8`, `u32`,
and `i32`. Indexed reads, writes, and element borrows require a full-width
`usize` bounds proof. The example also covers builtin lengths (including a
zero-length array), local aliases and reborrows, a direct helper call, and
parent reuse with preservation of an untouched word.

From the repository root, after installing the pinned Charon toolchain:

```sh
scripts/build-charon.sh --install-toolchain
cargo run --bin click -- import lock examples/rust-arrays/arrays.click
cargo run --bin click -- verify examples/rust-arrays/arrays.click
cargo run --bin click -- profile examples/rust-arrays/arrays.click
cargo run --bin click -- audit examples/rust-arrays/arrays.click
```

The `write` contract owns just the indexed word. Its caller keeps authority
over the rest of the array, so the helper's write does not erase the retained
word's value. No array length parameter is added to the sidecar signatures;
the exporter records the compiler-evaluated length in the fixed-array type.

This fixture does not establish support for local array construction,
by-value array copies, array-to-slice coercions, or checksum libraries.
