# First Rust verification example

`borrow.rs` is unchanged Rust source. `borrow.click` proves a scalar branch,
parent reuse after a mutable reborrow, a direct field helper call with a frame
for the other field, and a shared-field borrow across a disjoint write.

With an installed Click release, the committed artifact and lock verify offline:

```sh
click verify examples/basic-rust/borrow.click
```

To refresh with the installed frontend on Linux x86-64 GNU:

```sh
click install VERSION --rust
click import lock examples/basic-rust/borrow.click
click verify examples/basic-rust/borrow.click
```

Replace `VERSION` with the installed Click release version. The
`click.project.json` unit selects the pinned bundle automatically; no exporter
path or user Rust toolchain is needed. Unset the contributor override
`CLICK_CHARON` when using the installed frontend. Refresh reproduces the committed
lock for its matching release and profile. Ordinary verification needs neither
the compiler nor the frontend. See [Rust imports](../../docs/reference/rust.md)
for project units and frontend resolution.

For contributor builds, install pinned Charon and its compiler once:

```sh
scripts/setup-environment.sh
export CLICK_CHARON="$(scripts/build-charon.sh --install-toolchain)"
cargo run --bin click -- import lock examples/basic-rust/borrow.click
cargo run --bin click -- verify examples/basic-rust/borrow.click
```

Run commands from the repository root. Native artifacts and locks are checked
in; refresh regenerates them. Ordinary verification loads them without running
rustc. See the
[experimental Rust reference](../../docs/reference/rust.md) for supported
semantics and the compiler/translator trust boundary.
