# First Rust verification example

`borrow.rs` is unchanged Rust source. `borrow.click` proves a scalar branch,
parent reuse after a mutable reborrow, a direct field helper call with a frame
for the other field, and a shared-field borrow across a disjoint write.

With an installed Click release, the committed artifact and lock verify offline:

```sh
click verify examples/basic-rust/borrow.click
```

`click install VERSION --rust` adds the pinned Charon/compiler bundle for
Linux x86-64 GNU. Rust project units use it automatically at lock time. This
legacy example's config still names a contributor exporter path; to refresh
with the installed bundle, omit its `exporter` field, then run
`click import lock examples/basic-rust/borrow.click`. No compiler is run by
ordinary verification. See [Rust imports](../../docs/reference/rust.md) for
project units and frontend resolution.

For contributor builds, install pinned Charon and its compiler once:

```sh
scripts/setup-environment.sh
scripts/build-charon.sh --install-toolchain
cargo run --bin click -- import lock examples/basic-rust/borrow.click
cargo run --bin click -- verify examples/basic-rust/borrow.click
```

Run commands from the repository root. Native artifacts and locks are checked
in; refresh regenerates them. Ordinary verification loads them without running
rustc. See the
[experimental Rust reference](../../docs/reference/rust.md) for supported
semantics and the compiler/translator trust boundary.
