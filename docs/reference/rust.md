# Experimental Rust imports

Click accepts a small safe, monomorphic subset of Rust 2021 and 2024. Its Rust importer
uses pinned, unmodified [Charon](https://github.com/AeneasVerif/charon) after rustc
type and borrow checking. Every imported body follows the native ULLBC control
flow path into Click's shared execution, memory, and certificate rules.
Verification uses the same sidecars, tactics, and bounded engine as C and C++.
[Language coverage](coverage.md) compares the Rust subset with C and C++.

Charon is the extraction backend. On `x86_64-unknown-linux-gnu`, releases provide
an optional pinned frontend and compiler runtime through
`click install VERSION --rust`. Rust support remains experimental and covers
the subset listed in [Language coverage](coverage.md). Contributor builds use
`scripts/build-charon.sh`; ordinary verification of committed locks needs
neither Charon nor rustc.

The working example is
[`examples/basic-rust/borrow.rs`](https://github.com/clicklang/click/blob/master/examples/basic-rust/borrow.rs),
with its
[sidecar](https://github.com/clicklang/click/blob/master/examples/basic-rust/borrow.click).
It covers a scalar branch, a mutable reference helper that writes through a
local reborrow and then reuses its parent, and a caller proving a struct field's
final value while preserving its other field. A shared field borrow remains
stable while the disjoint field is mutated.

## Installed Rust frontend

`click install VERSION --rust` installs a bundle at
`CLICK_HOME/versions/VERSION/frontends/rust` (with the usual default
`CLICK_HOME`). The bundle's bounded `frontend.json` explicitly identifies
Charon, its paired driver, rustc, and the sysroot. Extraction checks the running
Click version, pinned Charon version/revision, compiler commit and host before
compiling. The Charon wrapper's paired-driver layout is validated against the
explicit driver entry. The bundle supplies its own target libraries and loader
paths; installed extraction does not search for rustup or use ambient compiler
flags. A missing bundle names `click install VERSION --rust`. A mismatched or
incomplete installed bundle names its exact frontend path to remove before
reinstalling: ordinary installation retains an existing bundle. Version errors
show the expected identity and the bounded identity actually reported. A
`CLICK_CHARON` override instead points to correcting/unsetting that override
and the source-build setup command. Hosts without a packaged bundle are
reported as unavailable rather than being given an install command that
cannot supply their platform.
Linux x86-64 GNU is the agreed launch host scope. The P1 frontend delivery
milestone is complete for that scope; additional host bundles and broader Rust
coverage are optional future work.

Rust project units use this frontend automatically. `CLICK_CHARON` is a
contributor override: a bundle directory selects that bundle, while an
executable selects the existing source-build path and its rustup-managed pinned
toolchain. The project schema and lock format are described
in [`click import`](cli/import.md#project-units) and
[project configuration](../concepts/own-project.md).

The release workflow builds Charon with `scripts/build-charon.sh --release`
and assembles the bundle with `scripts/package-rust-frontend.py`, including its
compiler libraries and license files. The installed-layout regression relocates
that bundle and an installed Click, extracts and verifies the unchanged basic
Rust example with crate-qualified sidecar names and the existing adler2
saved-checksum proof, repeats locking byte-for-byte,
checks mismatched identity refusal, then verifies after removing the frontend.

A separate release-packaging check consumes the exact archive and checksum
produced by `scripts/package-rust-frontend-archive.sh`. It starts with only a
Click launcher, invokes the real `click install VERSION --rust` command using
local release assets through its ordinary curl subprocess, relocates the
installed home, and verifies both examples with an empty PATH and no user
Rust toolchain. It checks repeated installation and locking, then offline
verification after removing the frontend. It also runs the
[C/Rust checksum demonstration](https://github.com/clicklang/click/blob/master/design/adler32/checksum-correspondence.md#reproduce)
from a relocated prepared directory, checking the complete C/Rust producer and
helper bodies, real incremental/saved-state clients and correspondence theorem
through locked imports after removing the frontend. The release workflow runs this check
before attaching assets to a release and on pull requests touching packaging.
The dedicated integration target stays outside the normal ten-minute gate;
there is no development-binary fallback for its release archive.

## Reproduce the example

Run `scripts/setup-environment.sh` once for Click's pinned stable toolchain.
Build pinned Charon and install its separate compiler with
`scripts/build-charon.sh --install-toolchain`, then run:

```console
cargo run --bin click -- import lock examples/basic-rust/borrow.click
cargo run --bin click -- verify examples/basic-rust/borrow.click
cargo run --bin click -- profile examples/basic-rust/borrow.click
cargo run --bin click -- audit examples/basic-rust/borrow.click
cargo run --bin click -- expand --claim update.contract --in-place examples/basic-rust/borrow.click
cargo run --bin click -- verify examples/basic-rust/borrow.click
```

Locked Rust imports also support focused proof tracing:

```console
cargo run --bin click -- verify --trace-proof update examples/basic-rust/borrow.click
```

Use a function or theorem name declared in the sidecar. `--trace-to LINE[:COLUMN]`
selects a written tactic within that proof. Only the named proof is checked;
other function contracts remain interfaces. Tracing validates the ordinary
import lock and does not rerun the compiler.

Every Rust example is a project: its `click.project.json` declares one Rust
unit per source, and a sidecar selects a unit with its ordinary `verifying`
path. A unit without a `crate` object is one `.rs` file compiled as a Rust 2024
library, with no other inputs:

```json
{"units": {"borrow": {"language": "rust", "sources": {"borrow.rs": {}}}}}
```

`click import lock` runs the compiler with a bounded process and writes
`.click/<unit>/<source>.ullbc` and `click.project.lock.json`. Ordinary
verification loads those files without executing the compiler. Source, unit
description, artifact, or profile changes require refresh, and a changed
source is named. The lock includes the compiler/extractor identity; after
updating the extractor or adapter semantics, refresh existing imports. The
normal example gate checks locked native inputs offline, while the nightly
gate's live Charon tests refresh and verify all 16 original Rust fixtures.

A Rust unit's lock entry uses the envelope shared with C and C++, and its
import identity the shared formula ([import.md](cli/import.md)); the `rust`
section records the lock schema, the source and the front end. Legacy
configurations still accept `"charon-trial"` as a backend compatibility alias.
Historical single-file crate/output labels inside serialized artifacts remain
stable.

Rust lock schema 9 records `frontend`: the Click release version, pinned Charon
version/revision, rustc commit and a SHA-256 identity of the complete extraction
and semantic profile. The front end's `identity` is the SHA-256 of that record,
so the import identity binds it to the unit, source closure and artifact. Local executable bytes, runtime paths and host
installation directories are absent. Source-built overrides use the same pins
and runtime handshakes, so equal inputs and extraction output give the same lock
as the packaged release. Extraction still detects executable changes during a
run. Single-file artifact source paths are normalized to their source filename;
crate paths remain relative to the unit root.

A schema-8 section, from releases before the `frontend` record, names the
exporter and Charon driver digests and the semantic profile it was prepared
under; it loads only while that profile is current. `click import lock`
refreshes it into schema 9; a Click release or semantic-profile change also
requires refresh. Normal verification never rewrites a lock.

## Locked crates and qualified declarations

A unit with a `crate` object gives an explicit crate root and compiler
configuration:

```json
"adler2": {
  "language": "rust",
  "sources": {"src/lib.rs": {}},
  "crate": {
    "name": "adler2",
    "edition": "2021",
    "features": ["std"],
    "roots": ["adler2::adler32_slice"],
    "files": ["src/lib.rs", "src/algo.rs"]
  }
}
```

This invokes rustc directly; it does not execute Cargo manifests or build
scripts, resolve third-party dependencies, or enable features implicitly.
Editions 2021 and 2024 are supported. Roots are explicit qualified paths.
All compiler-read inputs, including unused modules and included data, must
appear exactly once in `files`. rustc dep-info checks that closure. A mismatch lists missing entries in
`crate.files` and extra configured entries, with bounded lists. If a module or
include is omitted, rustc may fail before emitting dep-info because only the
configured files are copied into the private compiler snapshot. That error
retains rustc's filename/module diagnostic and explains how to check
`crate.files`; it never expands the compiler snapshot implicitly. Files must
be regular, use normalized relative paths, and stay inside the unit root without symlinks. Environment-dependent source macros are rejected.


Extraction compiles a private snapshot of those bytes. The aggregate source
hash covers every input, and configuration hashes bind the root, edition,
features, and entry points. Ordinary loading rechecks the full closure
without executing a compiler. Crate artifacts use the versioned
`click-charon-crate-v4` envelope; single-file units keep the earlier identity.

Module definitions and inherent methods retain compiler-resolved identities.
Proof identifiers encode tagged, length-prefixed path components, so `a::read`,
`b::read`, and `a_read` remain distinct even when their leaf names overlap.
Inherent methods include their resolved receiver type. Calls still follow
Charon's declaration IDs and execute imported bodies; names never grant a
library summary. Concrete assignment operators retain their trait,
implementation, signature, and associated-item checks across module paths.

Crate units support by-value returns of supported flat records, including owned
array fields and records with `Drop`. The concrete return layout enters the
kernel's aggregate-return interface: field values copy into fresh caller
storage, and Rust live flags transfer ownership once. Reference, array, and
nested-record returns remain unsupported. By-value flat-record parameters use
the kernel aggregate-parameter interface: each callee receives independent
storage. Compiler moves consume the caller’s live value; compiler copies
preserve it. Record copies require plain scalar or supported array fields
and no destructor. These ownership events are checked at calls as well as
local assignments. Array parameters by value remain unsupported.

Contracts take owned parameters as `input: RecordType`. Use
`old(input.field)` for entry values when the body modifies the parameter.
Its private bytes have internal ownership and cannot be declared as contract
input resources. Passing a pointer field still requires the pointee's own
resource clauses; copying a record grants no ownership over its pointees.

Crate units import local named scalar constants (`bool`, `i32`, `u8`, `u16`,
`u32`, and target-width `usize`) with straight-line arithmetic initializers.
Each initializer retains its qualified identity and executes its imported CFG;
constant reads call that body through the ordinary checked function interface.
Sidecars prove an initializer contract before using its value in callers.
For example, a `CHUNK_SIZE` initializer computing `5552 * 4` needs a verified
`uint64 <qualified-initializer>() { ensures result == 22208u64; }` contract.
Overflow and other arithmetic obligations remain checked. Statics, anonymous
or trait constants, generic constants, references, initializer branches,
dependencies on other constants, and `const fn` calls remain unsupported.

Concrete `core::default::Default` implementations on local records execute
their imported bodies. Dispatch checks the standard diagnostic identity,
qualified trait path, associated method, implementation ID, signatures, and
return type. Ordinary constructors use the same body and return path. Sidecar
contracts use `struct <qualified-record> <function>(...)` and can state
`ensures result.field == value;`; those contracts must verify before callers
can use them.

The unchanged adler2 example proves `Adler32::default` and `Adler32::new` return
`a = 1`, `b = 0`. Concrete assignment operators also accept supported
by-value record operands through the checked call interface. Selecting the
complete checksum loop now produces a locked, prepared import, and its
`MOD` and `CHUNK_SIZE` initializer contracts verify. Its unchanged whole body
proves bounds, termination, and both final checksum fields against the common
specification for canonical seeds and lengths through 2,147,483,647 bytes,
including full batches and both remainders. General trait dispatch and arbitrary Rust
crates remain outside the supported subset.

## Signatures in Rust syntax

A sidecar for a Rust source states a function's signature as Rust does,
with Rust type names, and cast with `as`:

<!-- verified-example: tests/fixtures/rust-verification/fn_signatures.click -->
```click
verifying "borrow.rs";

fn add_byte(sum: u32, byte: u8) -> u32 {
    requires sum <= 4294967040u32;
    ensures result == sum + byte as u32;
} by { execute(); simp(); }

fn times_three(value: u32) -> u32 {
    requires value <= 1431655765u32;
    ensures result == value * 3u32;
} by { execute(); simp(); }

fn reduce(value: u32) -> u32 {
    ensures result == value % 65521u32;
} by { execute(); simp(); }
```

A Rust source's function contracts require this form. A C-shaped signature
is refused with a suggestion of the `fn` spelling. A field through a
reference is `p.f`; `p->f` is refused. The
sidecar parser accepts every Rust integer and float type name, `bool`, `()`,
and a struct by name, but the importer admits only the types in
[Supported semantics](#supported-semantics); `usize` and `isize` are 64 bits. `expr as T` takes a
scalar type and binds as in Rust, tighter than a binary operator.

A parameter may be a reference, `&T` or `&mut T`, to a scalar or a struct.
The contract names what it refers to as Rust does: `*value` for the
referent and `parent.left` for a field. The type does not grant authority;
the contract still states `views` or `owns`. Lifetimes may be written or
left out, `fn pick<'a>(value: &'a u32) -> u32`; the contract does not use
them. Type parameters are limited to the supported
[callable bounds](#function-pointers-and-named-contracts) and
[crate trait bounds](#trait-method-interfaces). A tuple struct's field is
named by its position, `self.0`.

A diagnostic about a function whose signature is written this way, and the
proof `click expand` writes for it, spell its places the same way: a
slice's length `bytes.len()`, a cast `(x as u32)`, and a field through a
reference `p.field`.

<!-- verified-example: tests/fixtures/rust-verification/references.click -->
```click
verifying "borrow.rs";

fn choose(x: i32) -> i32 {
    requires 0 <= x;
    ensures result == (if x < 7 { x + 1 } else { 7 });
} by {
    execute();
    simp();
}

fn set_seven(value: &mut i32) {
    owns *value;
    ensures *value == 8;
} by {
    execute();
    simp();
}

fn update(parent: &mut Pair) -> i32 {
    owns parent.left;
    owns parent.right;
    ensures parent.left == 8;
    ensures parent.right == old(parent.right);
    ensures result == 8;
} by {
    execute();
    simp();
}

fn shared_field(parent: &mut Pair) -> i32 {
    owns parent.left;
    views parent.right;
    ensures parent.left == 7;
    ensures result == old(parent.right);
} by {
    execute();
    simp();
}
```

A slice parameter, `&[T]` or `&mut [T]` with a scalar element, is one name.
`bytes.len()` is its length, `*bytes` is the whole slice, and its elements
and ranges are indexed as a pointer's are. An index or a range bound keeps
its `usize` type, so nothing is cast and the contract states no bound on the
length:

<!-- verified-example: tests/fixtures/rust-verification/slices.click -->
```click
verifying "borrow.rs";

fn length(bytes: &[u8]) -> usize {
    ensures result == bytes.len();
} by { execute(); simp(); }

fn read(bytes: &[u8], index: usize) -> u8 {
    requires index < bytes.len();
    views *bytes;
    ensures result == bytes[index];
} by { execute(); simp(); }

fn write(bytes: &mut [u8], index: usize, value: u8) {
    requires index < bytes.len();
    owns *bytes;
    ensures bytes[index] == value;
} by { execute(); simp(); }

fn first(bytes: &[u8]) -> u8 {
    requires bytes.len() == 4;
    views bytes[0..4];
    ensures result == bytes[0];
} by { execute(); simp(); }

fn increment_first(bytes: &mut [u8]) {
    requires bytes.len() == 4;
    requires bytes[0] < 255;
    owns bytes[0..4];
    ensures bytes[0] == old(bytes[0]) + 1;
} by { execute(); simp(); }

fn empty(bytes: &[u8]) -> bool {
    ensures result == (bytes.len() == 0);
} by {
    if bytes.len() == 0 { execute(); simp(); }
    else { execute(); simp(); }
}
```

A `bool` result is a specification `bool`
([Booleans](language/index.md#booleans)): `ensures result;` claims it is
`true`, and, as in Rust, a parenthesized comparison is a `bool` value, so
`ensures result == (bytes.len() == 0);` states it exactly. Outside a
parenthesized operand a comparison remains a proposition, and a C or C++
sidecar keeps every comparison a proposition. A `bool` parameter is a claim
too: `ensures early implies result == 7;`. Rust has no cast to `bool`, so
`x as bool` is refused.

### Integer literals

An unsuffixed literal takes its type from what it is compared or combined
with, so `bytes.len() == 4` compares two `usize` values. Rust sidecars accept
decimal literals and the Rust radix prefixes `0x`, `0o`, and `0b`. Underscore
separators are accepted in the digits and before a suffix, as in
`65_535u16`, `0xff_ff_u16`, and `0b1_010usize`.

A suffix fixes the literal's native type: `i8`, `i16`, `i32`, `i64`, `isize`,
`u8`, `u16`, `u32`, `u64`, or `usize`. On the pinned target, `isize` and
`usize` are 64 bits. These are specification integer types; imported source
coverage is defined under [Supported semantics](#supported-semantics).
Floating-point suffixes and 128-bit integer suffixes are not supported.

A suffixed literal must fit its type; it is never truncated to make it fit.
A signed minimum, such as `-2_147_483_648i32` or `-(0x8000_0000i32)`, is
accepted under unary minus. The same positive magnitude is out of range.
Negating an unsigned suffixed literal is refused. Unsuffixed literals retain
contextual typing, including arbitrary-precision mathematical `Integer`
values when no native type is required.

<!-- verified-example: tests/fixtures/rust-verification/integer_literals.click -->
```click
verifying "literals.rs";

theorem literal_forms(word: u16, index: usize, signed_word: i32) {
    requires word == 0xff_ff;
    requires index == 0b1_010;
    requires signed_word == -0x8000_0000;
    ensures word == 65_535u16 by { assumption(); }
    ensures index == 0o12usize by { assumption(); }
    ensures signed_word == -2_147_483_648i32 by { assumption(); }
}
```

### Pure functions, predicates and theorems

A Rust sidecar's pure functions, predicates and theorems, their quantifier
and `let` binders, and algebraic datatype fields take Rust types too: the
scalars (`u8`, `i32`, `u32`, `u64`, `usize`, `bool`, ...) and a raw pointer
to one or to a crate struct, `*const T` or `*mut T`. Such a function takes values, not borrows,
and a reference `&T` is refused there. `x as T` casts in a body as in a
contract. The C spellings (`uint8`, `const uint8*`, `(int32)x`) still read
the same types.

A pure function may take a slice of scalars, `bytes: &[u8]`. As in a `fn`
signature, the slice is its pointer and a `bytes_len` length: the body reads
`bytes[k]`, `bytes.len()` and `*bytes`. A call passes it a slice parameter in
scope, such as a `fn`'s `bytes` or another pure function's, and the call
stands for the pointer and the length. A caller with no slice in scope, such
as a theorem over `p: *const u8` and `n: usize`, writes both, `size(p, n)`;
printed proofs write calls that way too, as `size(bytes, bytes.len())`. The
[byte-sum example](https://github.com/clicklang/click/blob/master/examples/rust-byte-sum/sum.click)
sums a prefix with `function prefix(bytes: &[u8], end: usize) -> Integer`,
whose body adds `to_integer(bytes[k] as i32)`, and calls it as
`prefix(bytes, i)`.

A method's contract is written in an `impl` block, `impl Type { ... }` or
`impl Trait for Type { ... }`, and its receiver is `self`, `&self` or
`&mut self`. It is the contract of the function the importer calls
`Type_name`. A trait with a type argument names its methods by that argument
too, as the importer does: the method of `impl MulAssign<u32> for Lanes` is
`Lanes_mul_assign_u32`, and of `impl AddAssign<&Lanes> for Lanes`,
`Lanes_add_assign_ref_Lanes`.

An item of a crate import is named by its path from the crate:
`fn quad::walk(bytes: &[u8]) -> u32`, a type `quad::Quad`, and
`impl adler2::algo::U32X4 { ... }`. The path stands for the name the
importer gives the item (`__rust_q_I4_quad_I4_walk`). A diagnostic prints
the path, `quad::walk.contract`, and `--claim` and `--trace-proof` take it.
An operator-trait method prints in Rust's qualified form: the method of
`impl MulAssign<u32> for adler2::algo::U32X4` is
`<adler2::algo::U32X4 as MulAssign<u32>>::mul_assign`, a reference or by-value
argument reads `<T as AddAssign<&T>>::add_assign` or
`<T as AddAssign<T>>::add_assign`, and `impl Default for adler2::Adler32` is
`<adler2::Adler32 as Default>::default`. A crate trait is named by its path,
and its method's implementation prints as
`<trait_methods::Square as trait_methods::Shape>::area` ([trait method
interfaces](#trait-method-interfaces)). `--claim` and `--trace-proof` take
that form, the importer's name, or a `FILE:LINE` location in the sidecar
([claim labels](cli/expand.md#claim-labels)). The importer names an inherent method by the
module its `impl` block is in, which Rust does not write: the method is
found in the import by its type and name, of which Rust allows one.

<!-- verified-example: tests/fixtures/rust-verification/impl_blocks.click -->
```click
verifying "borrow.rs";

impl Drop for Guard {
    fn drop(&mut self) {
        requires separate(memory(*self), memory(self.slot[0..1]));
        owns self.slot;
        owns self.saved;
        owns *self.slot;
        ensures self.slot == old(self.slot);
        ensures self.saved == old(self.saved);
        ensures *self.slot == old(self.saved);
    } by {
        execute();
        simp();
    }
}

fn cleanup(value: &mut i32) {
    owns *value;
    ensures *value == 42;
} by {
    execute();
    simp();
}
```

A reference to an array, `&[T; N]` or `&mut [T; N]` with a scalar element,
is the pointer to its first element. The length is the type's, so the
contract writes it, `views bytes[0..4]`
([`examples/rust-array-slices`](https://github.com/clicklang/click/blob/master/examples/rust-array-slices/arrays.click)).

A signature the importer cannot lower is refused in the sidecar too: an
array or slice by value, a reference to a reference or to `()`, and a slice
or array whose element is not a scalar. `fn` in a C or C++ sidecar is
refused. Click's own words (`requires`, `ensures`, `owns`, `result`, the
tactics) are the same in every language.

### Function pointers and named contracts

A sidecar callable parameter must match the source signature. A mismatch
reports both types in C spelling, such as `uint32 (*)(uint32)` against
`int32 (*)(int32)`.

A parameter of a safe Rust-ABI function-pointer type of scalar parameters and
a scalar or unit result, `f: fn(i32) -> i32`, is a callback, as in C. A named
contract is written as a Rust item, `contract fn Doubling(x: i32) -> i32 {
requires ...; ensures result == x + x; }`, and `requires Doubling(f);` gives
a call through `f` that contract, and a function passing its own `f` on
needs the contract too. Passing a function item, `apply(twice, x)`,
reifies it as a pointer; the caller's proof needs `twice` to meet the
contract, which Click checks at the call from `twice`'s own contract. When
the two contracts agree only by a proof, a refinement theorem shows it,
naming the crate function as a value by its path, as Rust passes it:
`theorem twice_is_doubling() { ensures Doubling(function_pointers::twice) by
{ unfold(Doubling); simp(); } }`, and the caller's proof applies it,
`apply(twice_is_doubling());`. The diagnostic that refuses the call suggests
that theorem. The importer reads Charon's `CastKind::FnPtr` of a
crate function item and its `FnOperand::Dynamic` call through a local, and
refuses unsafe or foreign function pointers and pointers of non-scalar
parameters
([`design/charon-trial/function-pointers`](https://github.com/clicklang/click/blob/master/design/charon-trial/function-pointers/callback.click)).

A named contract's value parameter is written with a Rust type,
`contract fn Adds(x: i32) -> i32 { let amount: i32; ensures result == x +
amount; }`, and attached with `requires Adds(f, { amount: k });`, as in C
([`design/charon-trial/parameterized-contracts`](https://github.com/clicklang/click/blob/master/design/charon-trial/parameterized-contracts/adds.click)).

A closure that captures nothing can be passed for such a pointer,
`apply(|y| y + y, x)`. The sidecar names it as rustc does, by its enclosing
function and its index there: `fn closures::caller::{closure#0}(y: i32) ->
i32 { requires ...; ensures ...; } by { ... }`, verified like any function,
and the caller's proof shows it meets the contract the callee requires of
the pointer. The importer keeps the closure's `Fn::call` body, rewritten as
a function of the closure's parameters, and reads Charon's cast of the
generated `ClosureAsFn` function as the closure's address. A closure called
directly is refused
([`design/charon-trial/closures`](https://github.com/clicklang/click/blob/master/design/charon-trial/closures/closure.click)).

A `&dyn Fn(i32) -> i32` parameter of scalar parameters and result is a
callback as a `fn` pointer is, and a closure passed for it may capture
variables, `shift(&|y| y + k, x, k)`. The closure's contract names its
captures as its body does, `fn capturing_closures::caller::{closure#0}(y:
i32) -> i32 { requires 0 <= k and k <= 1000; ensures result == y + k; }`,
and the callee states what it needs with a parameterized contract,
`requires Adds(f, { amount: k });`. Creating the closure gives a function
value carrying the closure's contract with its captures fixed to the values
captured, and a call requiring another contract of it holds when that
contract refines the required one, the caller's facts about the captured
values included. The refinement uses exact routes and the condition
decider, not search: a capture of `k + 1` whose bound follows from a bound
on `k` is not shown. A shared borrow of a scalar is read when the closure
is created, which safe Rust's freezing of the borrowed variable makes
exact, and a `move` capture is copied. A closure that captures nothing is
its function's address. Captures by mutable reference, `FnMut` and
`FnOnce` callees, and non-scalar captures are refused
([`design/charon-trial/capturing-closures`](https://github.com/clicklang/click/blob/master/design/charon-trial/capturing-closures/closure.click)).

An `impl Fn(i32) -> i32` parameter, or one of a type parameter bound by
`Fn`, `fn apply<F: Fn(i32) -> i32>(f: F, x: i32)`, is a callable value as
`&dyn Fn` is, and the head writes it as the source does; a head has no
`where` clause, so a bound the source writes there goes in the head's
parameter list. A closure passed
for it is checked as one passed for `&dyn Fn`, and a crate function item,
`apply(inc, x)`, is its function's address. The importer reads the
parameter's type from its `Fn` bound and the output type constraint, a
call `TraitClause::call` through it as a call through the value, and the
closure state or `FnDef` constant the caller passes as the value; one
verified body covers every instantiation. Other callable bounds, including
`impl FnMut` and `impl FnOnce`, generic function items, and non-scalar callable
parameters or results are refused; crate trait bounds follow the
method-interface rules below
([`design/charon-trial/impl-fn`](https://github.com/clicklang/click/blob/master/design/charon-trial/impl-fn/closure.click)).

### Trait method interfaces

A method of a crate trait, `pub trait Shape { fn area(&self, scale: i32) ->
i32; }`, has an interface: the sidecar's `trait` block states it, with the
trait named by its path and no proof, as an `extern fn` is declared,
`trait trait_methods::Shape { fn area(&self, scale: i32) -> i32 { requires 0
<= scale and scale <= 1000; ensures scale < result and result <= 3001; } }`.

A call through a trait bound, `shape.area(scale)` for `shape: &T` and
`T: Shape`, or through a `&dyn Shape`, is checked against the interface, as
a call of an `extern fn` is: its caller establishes the `requires` and has
only the `ensures`. The head writes a bound parameter as the source does,
`fn trait_methods::total<T: trait_methods::Shape>(shape: &T, scale: i32)`
or `shape: &dyn trait_methods::Shape`. A call on a known type,
`square.area(scale)`, is a call of that type's implementation, under its
own contract.

Each implementation is written in an `impl` block naming the trait and the
type by their paths, `impl trait_methods::Shape for trait_methods::Square
{ fn area(&self, scale: i32) -> i32 { ... } by { ... } }`, and verified as
any method is. It inherits the interface: the interface's `ensures` join its
own, labeled `<trait_methods::Circle as
trait_methods::Shape>::area.interface_ensures_0`, and its proof establishes
them all; an implementation that writes no `requires` takes the
interface's. The inherited clauses are read with the implementation's own
names for its parameters: `Square`'s `area` names `scale` as `factor`. It may accept more calls than the
interface, a wider precondition, and its `requires` are checked to follow
from the interface's by the check that forms a named contract at `&f`,
which reads each clause exactly or decides a bare comparison: `requires 0
<= scale; requires scale <= 2000;` follows from `requires 0 <= scale and
scale <= 1000;`. An implementation whose `requires` do not follow is
refused, naming both, as is one with no contract. Without a `trait` block,
a call through the trait has no contract.

A default method, `fn twice(&self, scale: i32) -> i32 { self.area(scale) +
self.area(scale) }` in the trait, has its interface written in the `trait`
block with the proof of its default body: `fn twice(&self, scale: i32) ->
i32 { requires ...; ensures result <= 6002; } by { execute(); simp(); }`.
The body is verified once, for every type: a call of `area` in it is a call
through the trait, under `area`'s interface, and with object state it holds
the object as any method of the trait does. A call of `twice` through a
bound or `&dyn` is checked against its interface; a call on a type whose
`impl` keeps the default, `square.twice(scale)`, is a call of the default
body, with the struct packed into its object as for a generic call. An
`impl` that writes its own `twice` inherits and refines the interface as
for any method
([`design/charon-trial/trait-methods`](https://github.com/clicklang/click/blob/master/design/charon-trial/trait-methods/shapes.click)).

The interface's receiver is a reference to a value of a type it does not
know: the interface reads nothing through `self` and holds none of its
resources, except its trait's object state (below), so an implementation whose contract needs the receiver's
fields does not refine it. Every implementation a call can reach is in the
import, since a generic call names its instance's implementation and a
`dyn` coercion its vtable, and each one is checked. The importer refuses a
crate trait with const generics, associated items, or supertraits, a method
that is generic or takes no `&self` or `&mut self`,
non-scalar parameters or results, an implementation for anything but a
crate struct, and a generic implementation other than one whose type
parameters are its trait's arguments (below)
([`design/charon-trial/trait-methods`](https://github.com/clicklang/click/blob/master/design/charon-trial/trait-methods/shapes.click)).

A crate trait may have type parameters, `trait Scale<T> { fn scale(&self,
x: T) -> T; }`. Each instance the crate implements or calls through,
`Scale<i32>`, is its own interface: its methods are the interface functions
`generic_traits::Scale<i32>::scale`, and its implementations are
`<generic_traits::Square as generic_traits::Scale<i32>>::scale`. A sidecar
may state every instance's interface once, in a block naming the type
parameters, and an instance's in a block naming its types; an instance's
interface is the generic block's clauses with its types for the
parameters, then its own block's. `trait generic_traits::Scale<T> { fn
scale(&self, x: T) -> T { ensures result != x; } }` binds every instance,
and `trait generic_traits::Scale<i32>` adds `requires 0 <= x and x <= 1000;
ensures x < result;` at `i32`. An implementation inherits and refines its instance's interface, labeled
`interface_ensures_0` onward in that order, and a call through `S:
generic_traits::Scale<i32>` or `&dyn generic_traits::Scale<i32>` assumes
it. The generic block is also checked once for every type, whether or not
the import uses an instance: its interface, `generic_traits::Scale<T>::scale`,
is lowered with `T` an abstract type, whose values have `==` and `!=` and
nothing else. A clause that needs more, `ensures x < result;`, means
something at some types only and is refused there ("the generic interface
... does not mean something at every type"); it belongs in an instance's
block. A generic block whose object carries state (below) is read at each
instance only. An instance is taken at `i32`, `u8`,
`u16`, `u32`, `usize` or `bool`, and the importer refuses a default method
of a generic trait
([`design/charon-trial/generic-traits`](https://github.com/clicklang/click/blob/master/design/charon-trial/generic-traits/shapes.click)).

Generic code is verified once for every type. An implementation whose type
parameters are its trait's arguments, `impl<T> Keep<T> for Echo`, and a
function generic over a type parameter bound by nothing but `Copy` or
`Clone`, `fn pick<T: Copy>(first: bool, a: T, b: T) -> T`, are imported once
with `T` an abstract type, and the sidecar writes them so, `impl<T>
generic_impls::Keep<T> for generic_impls::Echo { ... }` and `fn
generic_impls::pick<T: Copy>(...)`. A value of `T` is passed, returned,
held in a local and compared with `==` and `!=`; the body is proved once,
and the implementation refines the generic block's interface. A call at
scalar types, `echo.keep(x)` with `x: i32`, calls the instance
`<generic_impls::Echo as generic_impls::Keep<i32>>::keep`, which the import
declares and whose contract is the generic function's at those types: a
clause that reads its abstract values only by `==` and `!=` means the same
at every type. A type parameter is instantiated at `i32`, `u8`, `u16`,
`u32`, `usize` or `bool`, or at an abstract type of the calling generic
code: `read_twice<U: Copy>` calling `read(cell)` calls `read<U>`, whose
contract is `read`'s with `T` read as `U`, and a call at the callee's own
parameter names calls the generic function itself. A reference to a value
of `T`, `&T` or `&mut T`, points at one value of `T` in memory, a word as a
generic struct's field is: `fn peek<T: Copy>(value: &T) -> T { views
*value; ensures result == *value; }` reads it, and a caller at `u32` lends
`&mut slots.a` as it lends any `&mut u32`
([`design/charon-trial/generic-refs`](https://github.com/clicklang/click/blob/master/design/charon-trial/generic-refs/refs.click)).
A generic block whose object carries state is refused
([`design/charon-trial/generic-impls`](https://github.com/clicklang/click/blob/master/design/charon-trial/generic-impls/shapes.click)).

A generic struct, `struct Cell<T> { value: T, count: u32 }`, holds values of
its type parameters in memory. Each instance a type names is a record of its
own, spelled with its arguments in the sidecar, `generic_structs::Cell<T>` in
generic code and `generic_structs::Cell<i32>` in a caller. Rust fixes no
layout for a generic struct and safe code reads none, so Click lays each
instance out in declaration order: a scalar field at its size and alignment,
a field of an abstract `T` at eight bytes. A generic function over the
struct, `fn read<T: Copy>(cell: &generic_structs::Cell<T>) -> T { views
cell.value; ensures result == cell.value; }`, is verified once: a store of a
`T` value into a field and a load from it are value moves, and two fields of
`T` are two values. Each instance a call names has the generic function's
signature and clauses at its types, read again at the instance's own layout:
`read<i32>` reads `Cell<i32>`'s `value` at its offset. A sidecar does not
write an instance's block; `fn generic_structs::read<i32>(...)` is refused.
The struct's own methods are written once in a generic `impl` block,
`impl<T: Copy> generic_structs::Cell<T> { fn get(&self) -> T { ... } by
{ ... } }`, named `generic_structs::Cell<T>::get`; a call at `u32` calls
`generic_structs::Cell<u32>::get`, whose contract is the block's at `u32`,
and an `impl` block at an instance, `impl generic_structs::Cell<u32>`, is
refused. A generic struct's field is of one of its type parameters or a
scalar type, its `impl` blocks are inherent and name its parameters in
order, and it has no `Drop`
([`design/charon-trial/generic-structs`](https://github.com/clicklang/click/blob/master/design/charon-trial/generic-structs/cells.click)).

A generic trait's object may carry state, as any trait's does (below): the
generic block's `function last(self) -> T;` and `function items(self) ->
List<T>;` are fields of each instance's own object,
`bags::Bag<i32>::object`, at the instance's types, and an `impl` of the
instance defines them, `function items(self) -> List<i32> {
List<i32>::Cons(self.value, List<i32>::Nil) }`. Its pack and unpack are
named for the instance, `<bags::Slot as bags::Holder<i32>>::__pack`
([`design/charon-trial/generic-trait-objects`](https://github.com/clicklang/click/blob/master/design/charon-trial/generic-trait-objects/shapes.click)).

### Trait object state

A trait block may declare model functions of its object, `function
size(self) -> i32;`, which are the object's state: the trait's object is a
sealed abstract resource, `trait_objects::Shape::object`, with a field for
each function. A `&self` or `&mut self` method of the trait, a parameter
`x: &T` or `x: &mut T` with a `T: Trait` bound, and `x: &dyn Trait` or
`x: &mut dyn Trait` each hold the object `x` refers to, with no clause
written for it, and read its state as `size(x)`. A shared reference keeps
it, so the caller still knows `size(x)` after the call, and an `ensures`
reads it as it was at entry. A mutable one may change it: an `ensures`
reads the new state, `size(self) == half + half`, and `old(size(self))` the
state at entry, and the caller knows only what the `ensures` say. No proof
folds or unfolds the object: it has no body.

Each `impl` of such a trait defines every function from its type's
fields, `function size(self) -> i32 { self.side }`; an `impl` that omits
one is refused. Its methods are stated on the struct's own memory, `owns
*self` for `&self` and `&mut self`, with `size(self)` read as the definition in its own
clauses and in the interface's it inherits, and its proof is an ordinary
method proof. Its refinement is checked against the interface read on that
memory, an implementation's `contract fn` `..._iface`.

Where a struct reference becomes the object, at a call that instantiates a
bound type parameter with the struct or coerces it to `&dyn Trait`, the
importer brackets the call with the struct's pack and unpack. For a `&mut`
reference, pack consumes the struct's memory and produces its object, whose
fields are the definitions read on it, and unpack returns the memory with
the definitions equal to the fields. For a shared reference, the shared pack
views the memory and produces, beside the object, a resource that keeps the
memory lent until the shared unpack consumes both; nothing can change it
meanwhile, so the caller keeps every field. An implementation's `&self`
method likewise only views `*self`. A caller passing `&Square { side: 3 }`
therefore knows `size` is `3` and gets the interface's guarantee read with
that value, and keeps the fields `size` does not read (`tag_after_dyn`); one
lending `&mut square` gets back a struct whose fields the definitions equate
to the object's new state, so after `reset(&mut square, half)` it knows
`square.side == half + half` and nothing of the side it lent. A default
method's body holds the object as the trait's other methods do. Generic
traits are not yet supported
([`design/charon-trial/trait-objects`](https://github.com/clicklang/click/blob/master/design/charon-trial/trait-objects/shapes.click)).

### `extern` block functions

A `safe fn` declared in an `unsafe extern "C" { ... }` block has no body in
the crate, and a call to it needs no `unsafe`. The sidecar states the
contract Click trusts for it, as a C `extern` declaration does:
`extern fn extern_functions::clamp_reading(raw: i32) -> i32 { requires raw
>= 0; ensures 0 <= result and result <= 100; }`. A caller must establish the `requires` and may use only the `ensures`.
`extern fn` takes no proof, and a verified `fn` for such a declaration is
refused. Charon keeps no parameter names for a foreign item, so the head
names them; its types must be the declaration's. Parameters and the result
are scalars, or `()` for the result. An `unsafe fn` item and other ABIs are
refused, as their calls need `unsafe`. Functions of other crates are not
imported
([`design/charon-trial/extern-functions`](https://github.com/clicklang/click/blob/master/design/charon-trial/extern-functions/ffi.click)).

## Supported semantics

The scalar slice supports `i32`, `u8`, `u16`, `u32`, target-sized `usize`, booleans, unit returns, initialized scalar
and reference locals, branches, direct calls within the selected file,
references to `i32`, `u8`, `u16`, and `u32`, and plain structs with those integers or reference fields, field
access, and local reborrowing of reference-backed places. Arithmetic supports addition,
subtraction, multiplication, division, remainder, bitwise operations, comparisons,
and boolean operations. Unsigned shifts support `u8`, `u16`, `u32`, and `usize`; signed shifts
remain unsupported. Integer `as` casts preserve Rust truncation and bit
interpretation. Record
size, alignment, and field offsets come from rustc for the selected target;
Rust's default field order is not assumed.

Single-file units use Rust 2024; crate units select
2021 or 2024. The rest of the fixed profile is compiler commit
`923c95cdf5ba65cea505aa2ea829f578e1506ed8`, target
`x86_64-unknown-linux-gnu`, overflow checks enabled, panic abort, and MIR optimization level zero. Click must
prove that arithmetic overflow does not occur. Compiler acceptance alone does
not prove a functional claim or panic freedom.

Unsigned arithmetic has Rust's checked semantics: addition, subtraction, and
multiplication require overflow freedom, and division/remainder require a
nonzero divisor. A shift count must be nonnegative and less than the left
operand's width (8, 16, 32, or 64); shifting away high bits is allowed. Casts to `u8` and `u16`
retain the low eight and sixteen bits, respectively. Checks follow operand evaluation order and respect
`&&`/`||` short circuiting. Compound assignments use the same operations.
These obligations are checked during execution; C unsigned wrapping alone
cannot establish Rust panic freedom.

[`examples/rust-unsigned/arithmetic.rs`](https://github.com/clicklang/click/blob/master/examples/rust-unsigned/arithmetic.rs)
is a synthetic scalar regression covering byte accumulation, multiplication,
modular reduction, shifts, packing, truncation, and unsigned comparison. Its
[sidecar](https://github.com/clicklang/click/blob/master/examples/rust-unsigned/arithmetic.click)
uses ordinary Click contracts and tactics. Expansion can use the shared
`unsigned_sum_bound` arithmetic-certificate step for widened word bounds.
The [unchanged Adler2 computation](https://github.com/clicklang/click/blob/master/design/adler32/adler2/README.md)
is verified separately against the common checksum specification for lengths
zero through 2,147,483,647 bytes from canonical initial states. The unchanged
`write_slice` and `adler32_slice` wrappers compose checked bodies over the same
range, preserve input bytes, and prove field and packed checksum correctness.
A locked client also proves that two actual updates equal the full-input
checksum for every valid split over that range. The unchanged `from_checksum`
constructor is checked for every `u32` checksum. A separate
[resumed client](https://github.com/clicklang/click/blob/master/design/adler32/adler2/resumed.click)
restores the checksum of a checked prefix, updates with the suffix, and proves
the full-input checksum and byte preservation over the same length and split
bounds. Arbitrary saved words need not satisfy the canonical-seed preconditions
for an update.

```console
cargo run --bin click -- import lock examples/rust-unsigned/arithmetic.click
cargo run --bin click -- verify examples/rust-unsigned/arithmetic.click
```

## Byte slices and indexing

Shared `&[u8]` and mutable `&mut [u8]` parameters, local copies and reborrows,
builtin `.len()`, indexed reads and writes, and direct slice calls are supported.
Slice references lower to paired parameters: `bytes: &[u8]` becomes
`const uint8* bytes, uint64 bytes_len`; a mutable slice uses `uint8*`.
The generated `<parameter>_len` name must not collide with another parameter.
On the pinned target, `usize` is a 64-bit unsigned value, including lengths,
index literals, comparisons, casts, returns, and general scalar arithmetic.
Addition, subtraction, and multiplication require checked overflow freedom at
the full 64-bit width; division/remainder require a nonzero divisor. Bitwise
operations, checked shifts, and scalar compound assignments are supported.
Casts to `u32`/`i32` retain the low 32 bits, casts to `u8` retain the low eight
bits, and `i32 as usize` sign-extends before interpreting the bits as unsigned.
See [`examples/rust-usize`](https://github.com/clicklang/click/tree/master/examples/rust-usize)
for contracts over arithmetic, casts, computed indices, and length increments.

Every index checks `index < length` at the full target width before address
formation. Shared reads require `views`; writes require `owns`. Local slice
copies and calls preserve both pointer and length. The compiler checks borrow
legality; Click checks memory authority and the indexed values.

The [byte-slice example](https://github.com/clicklang/click/blob/master/examples/rust-slices/bytes.click)
uses variable-length contracts with existing memory ranges, as `read` and
`write` in "Signatures in Rust syntax" do. A range bounded by a `usize` has 64-bit bounds, so the contract states no
limit on the length. `.len()` alone needs no byte resource. General slice returns, range subscripts, indexed compound assignment, and
other slice element types remain unsupported. Supported shared slice splitting
is described below. Numeric contract casts are `x as i32`, `x as u32`,
`x as i64`, `x as u64` and the other scalar types, and like Rust `as` they
convert modulo 2^N. Use signed 64-bit widening to state full-width u32
addition guards, for example `(x as i64 + y as i64) <= 4294967295i64`.

## Shared slice splitting

The standard shared byte-slice method supports local destructuring:
`let (left, right) = bytes.split_at(mid)`. The exporter checks the resolved
core slice method and retains a `SliceSplit` operation. The receiver must be
a local `&[u8]`; both tuple elements must be plain bindings. General tuple
values, wildcard patterns, direct array receivers, mutable slice receivers,
and `split_at_mut` remain unsupported.

The receiver's pointer and length are captured before evaluating the midpoint,
which is evaluated once. Execution checks `mid <= bytes_len` at the full
64-bit `usize` width. The left slice keeps the original pointer and length
`mid`; the right starts at `bytes + mid` and has length `bytes_len - mid`.
No bytes are copied and no write authority is created. Subsequent reads use
the original input's `views` authority; the compiler rejects writes through
either shared result. Both results work with existing slice aliases,
indexing, `.len()`, and direct slice calls.

Pointer formation currently requires a checked `mid <= INT32_MAX` bound,
before narrowing the offset into the shared memory model. The original and
result lengths retain all 64 bits: metadata-only contracts can use larger
lengths when the midpoint fits. Splitting at zero or at the length is valid,
including an empty input; reading an empty result still fails its index check.

The [split fixture](https://github.com/clicklang/click/tree/master/examples/rust-split-at)
proves both result lengths and reads through each slice for variable split
points. Its regressions cover endpoints, full-width lengths and invalid split
indices, missing read authority, false values, and expanded proofs.

## Fixed arrays, copies, and checked indexing

Shared `&[T; N]` and mutable `&mut [T; N]` parameters support `u8`, `u32`,
and `i32` elements with concrete, compiler-evaluated lengths. A fixed-array
reference lowers to a typed pointer without a separate length parameter:
`&[u32; 3]` becomes `const uint32*`. The length remains in the prepared
execution and every indexed read, write, or element borrow checks
`index < N` at the full 64-bit `usize` width before forming an address.
Typed pointer arithmetic preserves element widths; word indices do not become
byte offsets. Array storage must fit the current signed-word memory model
(`N * sizeof(T) <= INT32_MAX`).

Compiler storage starts for local scalar arrays create checked fresh backing at
that point, including inside symbolic iterator loops. Plain record storage
starts also restore backing for array-field snapshot copies. The loop contract
need not list compiler-created local arrays as input resources. Re-entry checks
live loans and replaces the previous object's identity; initialization and
complete source/destination copy authority remain required.

Builtin `.len()`, local reference aliases and reborrows, and direct fixed-array
reference calls are supported. `.len()` requires no memory authority, including
for zero-length arrays. Reading any element of a zero-length array cannot pass
the checked panic obligation. Reads require `views` or `owns`, and writes
require `owns`; Rust reference types do not supply these resources implicitly.
The compiler checks conflicting borrows, while Click rejects false functional
claims and contracts that fail to establish bounds or memory authority.

The synthetic [fixed-array example](https://github.com/clicklang/click/blob/master/examples/rust-arrays/arrays.click)
covers all three element types, a checked element reborrow, a direct helper
call, parent reuse, and preservation of an untouched word. Its helper owns
only the indexed word, allowing the caller to retain the remaining storage.

```console
scripts/build-charon.sh --install-toolchain
cargo run --bin click -- import lock examples/rust-arrays/arrays.click
cargo run --bin click -- verify examples/rust-arrays/arrays.click
cargo run --bin click -- audit examples/rust-arrays/arrays.click
```

Initialized local arrays support literals (`[3u32, 5]`), repeats (`[value; 4]`),
and whole-array copies (`let copied = original`, `words = replacement`,
`*target = *source`). Each local has independent automatic storage. Constructor
operands are evaluated in source order before writing the destination; a repeat
operand is evaluated once, even when its length is zero. Copies capture all
source elements before writing and require read authority over the entire
source and write authority over the entire destination. Local arrays can be
borrowed, indexed, and passed to fixed-array reference parameters.

The synthetic [array-values example](https://github.com/clicklang/click/blob/master/examples/rust-array-values/arrays.click)
checks independent copies, replacing an array from its own elements, copies
through references, empty arrays, and constructor calls with observable effects.

Fixed byte arrays coerce to `&[u8]` and `&mut [u8]` in local initialization,
slice reassignment, and direct calls. The slice points at the original array
and carries its fixed length as 64-bit metadata; coercion allocates no storage
and grants no memory authority. Mutable sources can also coerce to shared
slices. Zero-length arrays support length-only calls without memory authority.
The compiler checks borrow validity, and Click still checks slice bounds and
the callee's `views`/`owns` requirements. See the synthetic
[array-to-slice example](https://github.com/clicklang/click/blob/master/examples/rust-array-slices/arrays.click).

By-value array parameters or returns, nested arrays, and non-byte slices
remain unsupported. Supported flat records can contain owned array fields,
including in crate-unit record returns described above. Imported
assignment-operator bodies support indexed `u32` updates, as checked by the
[assignment-operator fixture](https://github.com/clicklang/click/blob/master/design/charon-trial/assignment-operators/operators.rs).
The builtin length operation also supports non-byte fixed arrays by
recovering their fixed length; this does not enable non-byte slices or
general library methods.

Single-file units exclude modules and imports; crate units support
the locked module closure described above. Macros, semantic attributes,
dependencies, unsafe code, heap allocation, nested aggregate parameters,
reference returns, and other integer widths are outside this slice. Trait
dispatch and type parameters are limited to the forms described under
[callable bounds](#function-pointers-and-named-contracts) and
[trait method interfaces](#trait-method-interfaces); const generics
remain unsupported. Unsupported syntax
fails during extraction or direct lowering. This is not general Cargo-project
support.

## While loops and invariants

Unlabeled `while` loops, including nested loops, use the shared checked loop
rules. Sidecars can declare `invariant`, memory/resource clauses, and numeric
`decreases` measures. Entry and preservation are separate obligations;
arithmetic and indexing in the body retain Rust's panic-freedom checks.
A decreasing measure proves termination through the existing loop checker.
Charon locals with unique source names use those names in sidecars. Unnamed
and ambiguous locals use collision-checked `__rust_mir_ID` identities from the
locked artifact. These compiler identities can change when the artifact is refreshed.

Conditions currently support scalar comparisons, boolean combinations,
negation, casts, and builtin `.len()`. Calls, indexing, and arithmetic in a
condition require repeated preparation of checked operands and are rejected.
General iterators, `loop`, labels, `break`, and `continue` remain unsupported.
The copied-byte slice `for` form described below is supported.

[`examples/rust-loops/loops.rs`](https://github.com/clicklang/click/blob/master/examples/rust-loops/loops.rs)
and its [sidecar](https://github.com/clicklang/click/blob/master/examples/rust-loops/loops.click)
verify a scalar counter, checked accumulation, and a byte-slice walk with a
full-width `usize` counter. The walk uses `invariant i <= bytes_len` and
`decreases bytes_len - i`; slice access requires `views` authority.
Full-width range endpoints retain the target’s `usize` width; contracts using
signed indices must separately justify their conversions. The accumulator contract fixes the added value
to one. These are synthetic loop regressions, not a checksum-library proof.
Verification, profiling, auditing, and proof expansion use the shared engine.

```console
cargo run --bin click -- import lock examples/rust-loops/loops.click
cargo run --bin click -- verify examples/rust-loops/loops.click
```

The [byte-sum example](https://github.com/clicklang/click/blob/master/examples/rust-byte-sum/sum.click)
proves a functional loop over arbitrary input bytes. For slices of length
`0..=1000`, its unchanged Rust source returns the exact mathematical sum of
the input at function entry. Under `arithmetic "integer";`, a prefix fold
and the bound `0 <= total and total <= 255 * i` establish the result and
safety of every intermediate addition. It covers empty input and supports
profiling, audit, and expanded-proof reverification.

## Slice iterator loops

`for &byte in bytes`, `for byte in bytes`, and either pattern over
`bytes.iter()` support an immutable binding of type `&[u8]`.
The pinned compiler resolves `IntoIterator::into_iter` and `Iterator::next`;
the exporter checks their identities and the compiler's `Option` match before
lowering the loop. The `.iter()` method must resolve to the standard core
inherent slice method. Copied patterns read each yielded byte into a `u8`
binding; reference patterns bind a shared `&u8` address whose dereferences
require view authority. Shared-reference qualifiers survive local declarations.
The original Rust source stays unchanged.

The adapter retains Charon's native control flow, iterator calls, and `Option`
branches. A shared iterator named `iter` exposes `iter_cursor`,
`iter_remaining`, and `iter_live`; unnamed or ambiguous iterators use their
`__rust_mir_ID` identity as the prefix. A successful `next()` records the
shared element address in the returned option, advances the cursor, and
reduces the remaining length before entering the Rust body. Copied patterns
read that address; reference patterns bind it directly. An exhausted iterator
exits without a read or pointer advance, including for an empty slice.

There is no generated processed-count or index variable. Sidecars choose their
own properties of iterator state. The sum examples explicitly relate the cursor
to the original slice and derive a processed prefix as original length minus
remaining length; the remaining length also proves termination. This length is
the iterator's remaining slice metadata, represented as full-width `uint64`
for the locked 64-bit target. Signed prefix-index observations require a checked
range and conversion in the sidecar. Reads require view authority and
body arithmetic retains its panic checks. Immutable slice bindings keep the
original pointer and length stable; mutable bindings and slices are rejected.

[`examples/rust-iterators/sum.rs`](https://github.com/clicklang/click/blob/master/examples/rust-iterators/sum.rs)
and its sidecar prove the same exact byte sum as the `while` example for arbitrary
bytes and lengths `0..=1000`. Verification, profiling, audit, and expanded-proof
verification have regressions. The
[reference iterator fixture](https://github.com/clicklang/click/blob/master/examples/rust-iter-references/sum.rs)
proves the same sum using `for byte in bytes.iter()` and `*byte`. Missing views
and attempts to write through yielded shared references are rejected.
Shared iteration over fixed `i32`, `u8`, and `u32` arrays is also supported,
including borrowed arrays, local arrays, explicit `.iter()` calls, stored
`Iter` locals, and moves of the remaining iterator. See the locked
[array iteration example](https://github.com/clicklang/click/tree/master/design/charon-trial/array-iteration).
Moving an iterator retires its source; repeated exhaustion yields no element.
`.iter_mut()`, by-value array iteration, custom iterators, labels, `break`, and
`continue` remain outside this subset.

## Primitive unsigned conversions

Calls such as `u32::from(byte)` and `<u32 as From<u16>>::from(half)` support
compiler-resolved core `From` conversions between modeled unsigned scalar
types (`u8`, `u16`, `u32`, `usize`) when the source width is no greater than
the destination width. The Charon adapter validates the selected core
implementation, signature, and concrete types before constructing Click's
`IntegerFrom` operation;
lowering preserves the value and evaluates its argument once in source order.
These pinned standard-library primitive conversions are interpreted builtins;
their library bodies are not imported. Matching a method's spelling alone does
not authorize a conversion. User conversion implementations, `.into()`, bool
conversions, and general trait dispatch remain unsupported. The same adapter
rule applies inside supported owned-record functions.

`u16` has checked arithmetic, scalar references, and compiler-layout record
fields with two-byte storage. It does not extend the supported fixed-array
element or slice types. The
[integer-conversion fixture](https://github.com/clicklang/click/tree/master/examples/rust-integer-conversions)
checks shared reads, exclusive updates, preserved neighboring fields, and a
fixed checksum-style accumulator boundary case. It does not verify arbitrary
checksum updates or import adler2.

## Exact chunk iterators and remainder

The core shared byte-slice `chunks_exact(size)` method supports stored local
iterators, `for chunk in chunks`, `for chunk in &mut chunks`, and direct or
nested `for chunk in bytes.chunks_exact(size)` loops. The exporter checks the
resolved core slice method, the concrete `ChunksExact<u8>` type, and the
compiler's standard iterator/Option desugaring. It retains `ChunkDeclare`
and `ChunkFor` operations. `chunks.remainder()` checks the resolved core
inherent method and retains a `ChunkRemainder` expression. The receiver is
a shared byte-slice local; parameters or returns of iterator type, iterator
assignment/copying, adapters, and explicit `next()` calls are unsupported.

Construction captures the receiver before evaluating the size once, then
checks `size != 0`. Input lengths retain the locked target’s `usize` width.
For an iterator named `chunks`, the sidecar sees `chunks_cursor`,
`chunks_remaining`, `chunks_size`, `chunks_tail`, and `chunks_tail_len`.
The complete range has length `length - length % size`; its cursor initially
points at the original input. The fixed tail begins at the end of that
range and has length `length % size`. Chunk sizes and tail lengths retain
64 bits, as does the complete range's remaining length. The iterator does not
truncate metadata or impose an artificial `i32::MAX` construction limit.
Sidecars that express prefixes with signed indices must prove the relevant
range and value-preserving conversions.

Each successful `next` binds a shared byte subslice of length `size`, then
advances the cursor and subtracts that size from the remaining complete
range before the source body runs. The exhausted case performs no reads or
pointer advance. `remainder()` exposes the fixed tail, independently of how
many complete chunks were consumed. A saved remainder can be used after
consumption by value; borrowing the iterator allows subsequent method calls.
The compiler enforces moves and borrows. Neither method copies bytes or
creates write authority. Reads through chunks, aliases, calls, and tails
retain the original input's view requirements.

The [exact-chunk fixture](https://github.com/clicklang/click/tree/master/examples/rust-chunks-exact)
uses a cursor invariant and a divisibility invariant to describe the input
partition without a generated processed count. Regressions cover empty
input, exact multiples, short tails, nested loops, full-width chunk sizes,
zero-size rejection, false claims, missing bounds/views, and expanded proofs.
Mutable chunk iterators and non-byte slices remain unsupported.

## Moves and drops

[`examples/rust-move-drop/guard.rs`](https://github.com/clicklang/click/blob/master/examples/rust-move-drop/guard.rs)
constructs a guard, moves it, changes borrowed storage, and returns through two
paths. Its checked `Drop` contract restores the original storage value. The
caller proves the result was captured before cleanup and that the storage was
restored on both paths.

Local non-Copy structs support whole-value construction and moves, scope and
early-return cleanup, conditional initialization/moves, and explicit
`std::mem::drop`. Structs can have lifetime parameters and a local `Drop`
implementation. The compiler selects drop order and drop flags through its
ULLBC control flow; Click does not reconstruct cleanup
from source scopes. Destructor bodies require verified sidecar contracts.

Private checked live flags require a live source and dead destination for a
move, and consume the source. Reads and drops require a live value. Cleanup
must consume every destructor-bearing local before return. The flags prevent
stale struct bytes from justifying duplicate moves, duplicate drops, or omitted
cleanup. Struct storage uses existing checked stack allocation and typed field
loads/stores. Moving a reference field carries the same borrowed address; it
does not create allocation or deallocation authority.

Borrowing fields of local owned structs is supported. In
[`examples/rust-field-borrow/guard.rs`](https://github.com/clicklang/click/blob/master/examples/rust-field-borrow/guard.rs),
a child guard borrows its parent's saved field. Its destructor writes 42 to
that field, and the parent's destructor subsequently writes 42 to the caller.
Existing `owns` contracts suffice: the checked call planner consumes the
returned field owner and the retained storage fragments to supply the next
call. Each actual supplier is consumed once; views and gaps cannot supply
ownership. Regressions also cover parent mutation after explicit child drop,
disjoint mutable field borrows, false final-value claims, and compiler rejection
of conflicting parent access and use after move. The example passes verification,
profiling, audit, expansion, and re-verification without new Click syntax.

rustc establishes source borrow legality. These checks do not yet extract a
complete Rust loan protocol or infer ownership contracts from Rust types.

The adapter supports moving a reference field out of a plain local struct.
It still excludes general partial moves with cleanup, nested owned fields,
nested aggregate arguments or returns, unstructured control flow, heap owners such
as `Box`/`Vec`, and panic unwinding. Arithmetic, owned values, and loops use the
same native body representation; there is no whole-function coverage switch.

```console
cargo run --bin click -- import lock examples/rust-move-drop/guard.click
cargo run --bin click -- verify examples/rust-move-drop/guard.click
cargo run --bin click -- import lock examples/rust-field-borrow/guard.click
cargo run --bin click -- verify examples/rust-field-borrow/guard.click
```

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
that each modeled access is justified by the supplied resources.

For supported scalar functions, locked lowering issues checked local lease
births and explicit borrow-end operations. Straight-line code and structured
acyclic branches with a shared continuation are supported.
The supported pointees are `i32`, `u8`, `u16` and `u32`, with exact direct owned
footprints. Local copies or moves retain the same lease identity; a reborrow
creates a child that suspends its parent. Reads and writes use the ordinary
memory producers and their authority checks.

Ending frontiers follow scalar reads, writes, calculations and reference copies.
An indexed source pass propagates descendant uses to parents and emits nested
endings innermost first, including when several borrows end at one statement.
The kernel resolves each ending through its current invocation's live handle;
recovery does not depend on which alias name survives. Missing births, foreign
source identities, duplicate endings and parent endings with live children are
refused. Closing the outermost lease returns the original owned occurrence and
preserves current memory. Expired aliases cannot use that returned owner.

Across an `if`, scalar reads, writes and calculations can keep a borrow live
through the common continuation. A use in a deeper arm extends that borrow to
the corresponding common continuation; later uses can extend it further.
Nested borrows end innermost first.

Arm-local reborrows and reference copies are also supported when every such
reference stays inside its defining arm. Each branch scope checkpoints the
entry ledger, ends all references born there, verifies restoration of the exact
original owned occurrences, and clears the private arm-local reference slots
before restoring the exact entry ledger. Current writes are retained. Nested
scopes may borrow an entry reference temporarily, preserving it at scope exit.
The existing join still requires identical live loan state. Reference IDs are
never reused, and old copies remain invalid after scope reconciliation.

The source and sidecars require no additional lifetime annotations. Source
observations remain read-only. Reference assignments to an existing outer
binding, references escaping an arm, conditionally live borrow recovery,
early returns, shared borrow graphs, aggregate or addressable reference
transport, calls and loops still need source integration. Functions outside
the activated subset retain their existing lowering and have no local lease
coverage.

The trusted boundary includes the pinned compiler, exporter, semantic artifact,
and its translator. The lock detects stale or changed inputs; it is not an
attestation against somebody deliberately replacing the artifact and its lock.
Tests distinguish invalid Rust rejected by rustc from false functional claims
rejected by Click, and check the ordinary CLI and proof expansion path.
