# Experimental Rust imports

Click's first Rust frontend accepts a small safe, monomorphic subset of Rust
2024. It imports unchanged source through a repository-owned exporter using
pinned rustc typed HIR after type checking and borrow checking. The exporter
writes a typed JSON artifact; Click lowers that artifact directly to the shared
kernel execution vocabulary. Verification uses the same sidecars, tactics,
certificates, and bounded engine as C and C++.

The working example is
[`examples/basic-rust/borrow.rs`](https://github.com/clicklang/click/blob/master/examples/basic-rust/borrow.rs),
with its
[sidecar](https://github.com/clicklang/click/blob/master/examples/basic-rust/borrow.click).
It covers a scalar branch, a mutable reference helper that writes through a
local reborrow and then reuses its parent, and a caller proving a struct field's
final value while preserving its other field. A shared field borrow remains
stable while the disjoint field is mutated.

## Reproduce the example

Run `scripts/setup-environment.sh` once. Its full mode installs
`nightly-2026-06-16` with `rustc-dev` and the `x86_64-unknown-linux-gnu` target. Click itself continues to use
its separately pinned stable toolchain. Build the exporter with
`scripts/build-rust-exporter.sh`, then run:

```sh
cargo run --bin click -- import lock examples/basic-rust/borrow.click
cargo run --bin click -- verify examples/basic-rust/borrow.click
cargo run --bin click -- profile examples/basic-rust/borrow.click
cargo run --bin click -- audit examples/basic-rust/borrow.click
cargo run --bin click -- expand --claim update.contract --in-place examples/basic-rust/borrow.click
cargo run --bin click -- verify examples/basic-rust/borrow.click
```

The import configuration selects one `.rs` file, the exporter executable,
and an artifact output. Refresh runs the compiler with a bounded process and
writes the artifact and input lock. Ordinary verification loads those files
without executing the compiler. Source, configuration, artifact, or profile
changes require refresh. The saved lock includes the compiler/exporter identity.

## Supported semantics

The initial slice supports `i32`, booleans, unit returns, initialized scalar
and reference locals, branches, direct calls within the selected file,
references to `i32` and plain structs with `i32` fields, field access, and local
reborrowing of reference-backed places. Arithmetic supports addition,
subtraction, and multiplication, comparisons, and boolean operations. Record
size, alignment, and field offsets come from rustc for the selected target;
Rust's default field order is not assumed.

The fixed profile is Rust 2024, compiler commit
`01dfd79246f1b2d5f146616deff08223a840a9ae`, target
`x86_64-unknown-linux-gnu`, overflow checks enabled, and panic abort. Click must
prove that arithmetic overflow does not occur. Compiler acceptance alone does
not prove a functional claim or panic freedom.

Modules, imports, macros, semantic attributes, dependencies, unsafe code,
traits, generics, loops, heap allocation, aggregate values and returns, reference
returns, and other integer widths are outside this slice. Unsupported syntax
fails during extraction or direct lowering. This is not general Cargo-project
support.

## Borrow and proof boundary

rustc establishes source type and borrow legality. Click checks the functional
contract and memory access obligations of the extracted execution. `&mut T`
parameters use pointer-shaped sidecar parameters with explicit `owns` clauses;
shared references use explicit `views` where access is required. Borrowed
references carry no allocation or deallocation authority.

This frontend does not infer sidecar authority from a Rust reference. Contracts
must provide the resources they use. Reborrows of caller storage retain the
same modeled pointer: writes through the child are observed through its parent.
The compiler establishes when parent reuse is legal; the kernel establishes
that each modeled access is justified by the supplied resources. Production
move/drop rules and explicit resource suspension/recovery remain roadmap work.

The trusted boundary includes the pinned compiler, exporter, semantic artifact,
and its translator. The lock detects stale or changed inputs; it is not an
attestation against somebody deliberately replacing the artifact and its lock.
Tests distinguish invalid Rust rejected by rustc from false functional claims
rejected by Click, and check the ordinary CLI and proof expansion path.
