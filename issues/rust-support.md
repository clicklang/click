# P1: Support safe Rust and verify a shared C/Rust checksum specification

## Goal and priority

Deliver a useful, explicitly bounded safe-Rust verification path through
Click's existing proof language and checked engine. Then verify unchanged C
and Rust implementations of the same checksum against one mathematical
specification. This issue is P1 by user direction on 2026-09-30. General Rust
coverage remains later work; the Linux rbtree remains the key launch demo.
Rust frontend work can proceed alongside C/C++ work, with coordinated changes
to shared resource and execution rules.

There are two independently reviewable milestones:

1. **Experimental Rust support:** verify meaningful functional contracts over
   unchanged `.rs` source using Click sidecars, including scoped borrowing.
2. **Shared C/Rust library demonstration:** prove selected existing checksum
   implementations satisfy the same specification, establishing equality of
   their results under matched input and state conditions.

Ship and document the first milestone as soon as it is complete. Do not wait
for the library demonstration to announce the supported subset.
Both milestones must satisfy the architecture consolidation requirements below;
successful isolated feature fixtures are not sufficient evidence that the
features compose or that their representations scale.

## Unmet capability and required invariant

Click now has an experimental Rust source import and verification path. The
borrow fixture and move/drop guard verify unchanged Rust through shared Click
proof tooling. General library support and the shared checksum demonstration
remain unmet. The nested owned-field regression now verifies the unchanged
Rust source with final caller value 42 and rejects a claim of 1. Shared call
rules reserve the returned field and retained storage fragments exactly once.
Parent mutation after explicit child drop and disjoint mutable field borrows
also verify; conflicting borrows and use after move are rejected by rustc. See
[the supported subset](../docs/reference/rust.md) for exact bounds and
reproduction commands.

For supported source, compiler-established type and borrow guarantees must
survive translation into the checked execution model. Mutations, calls,
resource transfers, and recovery must preserve their meaning, and false
functional claims must be rejected. The C and Rust programs must satisfy one
shared specification without rewriting their implementation to suit the
verifier. Unsupported constructs must produce bounded, actionable diagnostics
rather than silently receiving C semantics.

## Existing evidence and architecture

Start with the [worked resource correspondence](../design/rust-resource-correspondence.md),
[language design](../design/supporting-more-languages.md), and
[stable views](../docs/internals/stable-views.md). The correspondence pairs
four Rust compiler/runtime witnesses with four independent resource traces
and three compiler rejection cases. Production shared-loan correspondence
also has checked tests. Exclusive child borrowing and value transport are
model-only; the small field model suspends the whole parent, more strictly
than Rust's field-sensitive rules. Disjoint range partitioning has separate
evidence and must be connected to any exclusive dependency representation.

Use a pinned rustc integration and reuse its type and borrow checking for the
supported safe subset. Select extraction boundaries by semantic coverage and
composition evidence. HIR versus MIR is not a contest with one universally
correct answer; the requirement is a consistent verification representation.
A complete lifetime/loan export or an independent borrow checker is not a
prerequisite unless the selected proof interpretation needs it. Retain Click
sidecars and checked proof operations when borrowing designs from other tools.

Map ordinary exclusive access to borrowed `owns` authority and ordinary shared
access to stable `views`. Keep allocation lifetime, access authority, and type
validity distinct: an `&mut T` does not grant deallocation authority, and a
Rust move transfers value resources rather than merely lending them. Sidecar
or ghost access must not introduce conflicting authority rustc never checked.

Keep one proof language and one bounded verification engine. Rust-specific
frontends belong beside the existing language modules; share kernel operations
where their semantics agree. Lock source identity, compiler/exporter version,
selected target/layout, semantic flags, and dependencies into prepared inputs.
Document the compiler and translator trust boundary. Do not introduce a
parallel Rust verifier or rename every C-prefixed type as a prerequisite.

## Current checkpoint

The first experimental frontend imports a pinned rustc typed HIR artifact for
single-file safe scalar/reference functions. The basic Rust example exercises
branching, a local reborrow followed by parent reuse, and a direct field helper
call with preservation of the other field, plus a shared-field borrow across
a disjoint write. Verification, profiling, auditing,
and expansion share the existing engine. See `docs/reference/rust.md` for the
exact subset and trust boundary.

This is an increment toward milestone 1, not its completion. The production
subset now includes whole-value moves, checked drops, nested field borrows,
and disjoint mutable field regressions. Explicit extracted loan authority
suspension/recovery and wider source coverage remain outstanding; source borrow
legality currently comes from the pinned compiler.

## Architecture consolidation before further library coverage

The 2026-10-02 review identified four design changes required for the long-term
frontend. Preserve the useful foundations: pinned compiler semantics and layout,
locked prepared inputs, explicit panic obligations, shared memory authority,
and checked proof certificates. Consolidate the representations in coherent
increments rather than replacing the proof engine or rewriting source programs.

### 1. Make supported operations compose with ownership

The exporter currently uses structured typed HIR for scalar/reference functions,
but switches a whole function to the narrower drop-elaborated MIR exporter when
any MIR local has a local record type. This is a semantic coverage cliff.
For example, a function returning `u32::from(x)` for `x: u16` imports, but adding
`let _guard = Guard { field: 1 };` makes the same conversion fail with
`MIR call outside direct local scalar/reference calls`. MIR arithmetic and
byte slices have separate restrictions, and owned-value MIR loops are rejected.

Introduce a common typed semantic body representation for evaluation, places,
checked operations, resolved calls, control flow, and ownership/drop events.
HIR may supply source structure and proof locations; MIR may supply resolved
evaluation and cleanup. Specify which compiler phase establishes each fact and
how source structure corresponds to semantic operations. Do not combine the
two by heuristic matching or maintain separate definitions of Rust arithmetic
and call semantics according to whether a function contains an owned record.

Acceptance:

- Existing supported conversions, arithmetic, references, arrays, slices, and
  iteration compose with modeled owned records, moves, and drops. Add tests that
  combine these features, including a guard surviving across a supported loop.
- Preserve evaluation order, single evaluation, checked overflow/bounds,
  short-circuiting, and cleanup on every supported exit. Negative functional,
  panic, permission, and duplicate-cleanup cases reach the appropriate boundary.
- Shared control-flow joins remain shared; body size and checking work do not
  grow with the number of paths. Preserve source attribution through lowering.

### 2. Keep array shape and bulk operations compact

Current local-array lowering enumerates every element in the aggregate layout;
`[value; N]` also builds an element-sized vector and emits N stores. Tiny source
such as `[0u8; 1_000_000]` can therefore generate a huge verifier program.
Four checksum lanes do not establish a scalable representation for buffers.

Represent array element type, length, repeated initialization, and whole-array
copies compactly, with range-based value and authority reasoning. An explicit
N-element source initializer may require N work; a repeated initializer must
not require N verifier operations merely because its runtime storage is large.
Preserve one evaluation of the repeated operand, including when N is zero.

Acceptance:

- Empty arrays, repeated initialization, explicit initialization, copies,
  aliasing/reborrows, element updates, and neighboring-byte preservation verify
  with the same source semantics and permission rules.
- Deterministic regressions vary repeat/copy length, explicit source initializer
  size, and unrelated context independently. Compact operations do not allocate
  one layout field, proof term, or generated store per represented element.
- Ordinary verification, expansion, and audit agree; no higher work budgets or
  specialized source rewrites compensate for representation growth.

### 3. Separate source identities and proof observations from lowering names

Functions, records, and locals currently cross the artifact boundary largely as
strings. Generated slice parameters and iterator state use names such as
`bytes_len` and `chunks_remaining`; valid Rust names can collide with them.
Sidecars also depend on these names and repeated `(int32)(uint32)` conversions.
Expression and statement variants lack systematic source spans.

Use compiler-resolved identities, typed place projections, and source locations
independently of display spelling. Add stable source-facing observations for
slice contents/lengths and iterator remaining ranges so representation changes
do not require rewriting every contract and invariant. Retain an explicit
mapping for readable diagnostics and checked expanded proofs. Migrate existing
sidecars deliberately rather than silently changing their meaning.

Acceptance:

- Shadowing and source names matching generated suffixes remain importable;
  qualified item identities support later modules and resolved method calls
  without depending on globally unique short names.
- Contracts and loop invariants use stable observations; generated temporary
  spelling and storage representation can change without changing the claim.
- Panic/permission diagnostics identify the original Rust operation. Expansion
  preserves identity and snapshot meaning and parses and verifies normally.
- Full-width Rust metadata remains intact. The current signed-word memory-range
  bound stays explicit until shared kernel support removes it; a nicer proof
  surface must not conceal that semantic restriction or truncate `usize`.

### 4. Centralize resolved library models and their trust assumptions

`From`, slice iteration, splitting, and exact chunks currently use separate
recognition and lowering paths. Keep compiler resolution, but replace the
growing collection of special cases with a common registry of supported
operations or instances. A model records the resolved item/type arguments,
compiler/profile requirements, preconditions, effects, panic behavior, and
whether its semantics come from verified imported code or a named trusted
interpretation. The same model must apply inside and outside owned functions.

Acceptance:

- Supported standard-library calls and instances share resolution and semantic
  dispatch. Lookalike user methods, unsupported implementations, and unmodeled
  instances fail promptly rather than receiving a model by spelling alone.
- Model identity participates in prepared-input compatibility; source/profile
  or model changes require the appropriate refresh and invalidation.
- Iterator models preserve actual state, exhaustion, shared bytes, and remainder
  coverage without generated processed-count shortcuts. Conversion models
  preserve values and evaluation order. Mutable/adapted forms require their own
  assessed resource and state transitions before being enabled.
- Documentation names trusted models individually. Checksum computation remains
  verified code; a library summary must not assume the checksum postcondition.

### Implementation references and delivery order

The inspected projects offer complementary designs:

- [Verus](https://github.com/verus-lang/verus/blob/main/source/CODE.md) translates
  Rust HIR/THIR to its own VIR, then to a statement-oriented representation and
  assertion IR. Borrow its separation of compiler integration, semantic IR,
  and proof backend, and study its
  [mutable-reference interpretation](https://verus-lang.github.io/verus/guide/mutable-references.html).
- [Creusot's body translator](https://github.com/creusot-rs/creusot/blob/master/creusot/src/translation/function.rs)
  translates MIR to FMIR; its
  [program backend](https://github.com/creusot-rs/creusot/blob/master/creusot/src/backend/program.rs)
  lowers that to Coma for Why3. It provides a complementary MIR-based example
  of keeping Rust semantic normalization separate from backend reasoning.
- [Charon](https://github.com/AeneasVerif/charon) extracts simplified MIR,
  resolved declaration/trait information, and source information into an
  independent representation. [Aeneas](https://github.com/AeneasVerif/aeneas)
  consumes its LLBC representation and translates a safe-Rust subset into pure
  functional models for proof assistants. Study the extraction and borrowing
  abstractions without replacing Click's existing memory and proof model.

The [2026-10-02 Charon assessment](../design/rust-charon-assessment.md) completes
the initial extraction comparison. The pinned candidate extracts an owned guard
combined with conversions, arrays, and borrowed iteration, rejects invalid
borrowing/moves, keeps repeated arrays compact and CFG joins shared, and extracts
the unchanged pinned adler2 path. This is extraction evidence, not checksum
verification. Its newer compiler, per-body MIR phase provenance, library models,
source/proof correspondence, and checked resource mapping remain adoption gates.

The [end-to-end adapter trial](../design/charon-trial/README.md) now routes checked
arithmetic and a restoring owned guard through ULLBC and the existing engine.
The borrowed-loop checkpoint now proves iteration, termination, and restoration
with a live guard, including zero iterations and the maximum signed bound.
It rejects unsupported CFG exits/entries and effectful guards; scaling checks
cover sequential loops and diamonds. Shared pointer framing retains exact alias
and separation premises, rather than inferring provenance from local storage.
Keep migration opt-in until the supported fixtures have equivalent coverage.
The conversions/arrays checkpoint now composes a resolved `u32::from` call,
repeated initialization, uniform whole-array copy, and restoring `Drop` guard.
Its shared compact initialization operation checks authority and initialization;
8-, 1024-, and million-element arrays retain bounded node count, storage, and
deterministic proof work. Empty initializer calls execute once. The snapshot
checkpoint below now adds copies after concrete element overrides and copies of
independently computed lanes; whole-array reassignment remains migration work. The byte-slice checkpoint now carries shared/mutable parameters,
full-width length metadata, dynamic read/write bounds, reborrows and local calls
through ULLBC, including restoring guard cleanup. `byte-slice-metadata-v1` checks
compiler-resolved length calls and paired pointer/length origins; typed indices
restore panic obligations removed by Charon's selected transform. Missing bounds
and authority, high-bit indices, and false cleanup claims are rejected. Metadata
work remains bounded for empty, small, million-byte and maximum-width lengths;
proof tools recheck the same certificates. Subslices, returned slices and slice
fields remain parity work. The stored exact-chunk checkpoint now
imports shared byte iterators, fixed remainders, owned moves, `IntoIterator`,
typed `next`/Option dispatch and natural loops through ULLBC. Checked liveness
rejects missing construction and duplicate moves; payload extraction requires
`Some`. The fixed-source loop proves that chunks reach the tail without gaps
and preserve the original bytes, including zero iterations. Full-width sizes,
empty/exact/short boundaries, permission failures, explicit matches and proof-tool
agreement have regressions; metadata work stays bounded across input lengths and
protocol normalization is indexed with linear scaling coverage. The named model
`shared-byte-chunks-exact-v1` is lock-bound. The nested checkpoint now composes
outer four-byte and inner two-byte iterators, proving termination, both byte
reads, and preservation for an eight-byte input. Nested natural regions have
linear analysis/emission scaling regressions at depths 8, 32, and 128; extra
exits and irreducible entries remain rejected. Duplicate compiler temporary
names have distinct identities without renaming the Rust source.
`byte-array-unsize-v1` checks concrete extent metadata, normalized reference types
and mutability, with compiler borrow checking and existing memory authority.
Shared/mutable coercions, dynamic indexing, empty and million-byte arrays,
negative metadata/type cases and proof-tool agreement have regressions.
The arithmetic checkpoint now accepts typed panic-mode unsigned division,
remainder and shifts, plus bitwise AND/OR/XOR and complement. The original
unsigned regression functions import unchanged, including reduction modulo
65521 and checksum packing. Width, zero-divisor, negative/oversized/high-bit
shift, unsupported mode and false-result regressions exercise the shared checked
engine. Shift counts preserve their source width through shared lowering, with
matching Charon and default-frontend proofs. `unsigned-checksum-operators-v1` is
lock-bound. The borrowed array-field checkpoint preserves compiler-selected
array offsets, element types, extents and shared/mutable qualifiers. Named and
tuple-field reads, indexed mutation with neighboring cells preserved, local
array-borrow calls, byte-field coercions and empty fields have verified probes.
One layout entry per field and bounded work at 4/1024/1,000,000 elements prevent
extent-dependent flattening. The lock names `borrowed-scalar-array-fields-v1`;
the owned uniform array-field checkpoint now adds construction, moves,
whole-field replacement, extraction and snapshot independence with neighboring
fields preserved. `compact-uniform-array-regions-v1` keeps complete byte authority,
source initialization, types, extents, qualifiers and active loans checked.
Lowered nodes and verification work remain bounded at 4/1024/1,000,000 elements;
consumed record flags reject duplicate moves. The
`compact-scalar-array-snapshots-v1` checkpoint now copies independently
computed lanes and sparse repeated storage, preserving values across source and
destination mutation, record moves and field replacement. Complete typed
coverage, snapshot-before-write ordering, ordinary proof-tool agreement and
bounded work at 4/1024/1,000,000 elements are tested. Symbolic/heap region writes,
opaque load runs and symbolic-address cached writes remain unsupported. The
`shared-scalar-array-iteration-v1` checkpoint now models stored `Iter<T>` and
`Option<&T>` for shared `i32`, `u8` and `u32` arrays through the same checked
reference-origin, Option and CFG dispatch machinery as exact chunks. Cursor,
remaining element count and move/live state retain both successful and final
exhausted transitions without generated processed counters. Borrowed and local
loops, explicit next calls, partial moves, empty arrays, order, read authority
and source preservation have probes; declaration/signature forgery, stale None
payloads and consumed state are rejected. Lowering and first-read proof work
remain bounded at 4/1024/1,000,000 elements. Mutable/by-value/adapted iteration,
iterator parameters/returns and general scalar slices remain later work. Next
add resolved custom operators for the unchanged checksum path, broaden iterator composition
proofs, and cover borrowed loops. Stable observations and broader iterator parity remain gates.
Establish stable source/proof observations and equivalent coverage before
switching production imports. Preserve source metadata and a
Click-owned semantic boundary; do not rebuild rustc's HIR-to-MIR semantics just
to retain syntax. Use the assessment's configuration rather than adopting an
unaudited preset. Then consolidate semantic
operations and identities, compact arrays, stable proof observations, and the
model registry in reviewable increments. Extend checksum syntax on top of these
boundaries rather than adding more incompatible paths. These are requirements
for closing this issue, not evidence that the changes have already landed.

## Initial assessment

Produce a small, reviewable extraction experiment over scalar branching,
struct-field mutation, and a local reborrow followed by parent reuse. Identify
how the chosen representation connects writes through the child to the value
subsequently observed through its parent. Record which facts rustc establishes
and which transitions Click checks. This assessment selects the boundary;
it is not itself completion of Rust support.

In parallel, inspect and pin the proposed library sources. Record their
reachable functions, Rust constructs, C compiler configuration, and proof
obligations. Use that concrete inventory to plan coverage; do not assume an
algorithm's simplicity means its optimized implementations are already supported.

The [pinned checksum assessment](../design/rust-checksum-assessment.md) records
zlib 1.3.1 and adler2 2.0.1, selected build configurations, reachable constructs,
and the shared specification. Unsigned `u8`/`u32` scalar arithmetic now has a synthetic regression with
checked panic obligations, casts, bitwise operations, and proof expansion.
Byte slices now have variable-length read/write contracts, 64-bit `usize`
metadata and bounds checks, existing `views`/`owns` authority, direct calls,
and checked expansion. Memory-access contracts currently bound length by
`INT32_MAX`. Fixed-array references now support `u8`, `u32`, and `i32` elements,
compiler-evaluated lengths, checked indexing and element borrows, `.len()`,
local aliases/reborrows, and direct calls. Bounds are checked at the full
target `usize` width before address formation; zero-length and oversized
indices, false values, missing authority, and conflicting borrows have
regressions. Local scalar arrays now support literal and repeat construction,
independent whole-array copies and assignment through references, and local
array borrows. Constructor evaluation order, one evaluation for repeats
(including empty arrays), self-copy, and full source/destination authority
have regressions. Fixed byte arrays now coerce to shared/mutable byte slices
in local initialization, slice reassignment, and direct calls, preserving
length and storage authority. Empty arrays and parent reuse have regressions.
General `usize` scalar arithmetic now includes checked addition/subtraction/
multiplication, division/remainder, shifts, bitwise operations, compound
assignments, and integer casts at the full 64-bit target width. Computed slice
indices and length increments, full-width boundary values, panic rejection,
and proof expansion have regressions. Unlabeled HIR `while` loops now use
shared invariants, resource clauses, and decreasing measures, with scalar
accumulation, full-width byte-slice iteration, nested loops, panic rejection,
and checked expansion regressions. Guards currently exclude calls, indexing,
and arithmetic; general iterator/control-flow coverage and owned-value MIR loops
remain outstanding. The [byte-sum fixture](../examples/rust-byte-sum/README.md)
now proves an unchanged loop summing arbitrary bytes in slices of length
`0..=1000`, using an exact mathematical prefix fold, a full-width `usize`
counter, intermediate overflow bounds, and a decreasing measure. False sums,
incorrect invariants, missing bounds, and expanded proofs have regressions.
This is synthetic functional accumulation; the pinned checksum libraries
remain unverified.
The [slice iterator fixture](../examples/rust-iterators/README.md) proves the
same sum with unchanged `for &byte in bytes` source, using compiler-resolved
iterator calls, copied byte bindings, explicit cursor/remaining-slice state, and
shared loop rules. No processed count is generated; its prefix invariant is
authored in the sidecar.
The [reference iterator fixture](../examples/rust-iter-references/README.md)
proves the same sum with `for byte in bytes.iter()` and shared-reference
dereferences. Direct slices and `.iter()` support both copied and reference
bindings, with read authority and shared-reference write rejection regressions.
Only immutable shared byte-slice bindings are supported; mutable iteration,
stored byte iterators, and iterator control flow remain outstanding.
Shared byte-slice `chunks_exact` now supports stored and direct iterators,
consuming loops and loops borrowing the iterator mutably, shared subslice
bindings, and a fixed `remainder` before or after consumption. Explicit cursor,
remaining complete-byte length, chunk size, and tail state model the iterator;
no processed count is generated. The
[exact-chunk fixture](../examples/rust-chunks-exact/README.md) proves that the
chunks reach the tail without gaps and preserve every input byte for arbitrary
inputs of length `0..=1000`. Empty inputs, exact multiples, short tails,
full-width oversized chunks, one evaluation of the size, nested loops, shared
write rejection, zero-size panic rejection, and checked expansion have
regressions. Mutable chunks, iterator copies/adapters, and explicit `next`
remain outstanding; this fixture does not verify adler2.
Checked `u16` scalars, references, and compiler-layout record fields now support
primitive lossless unsigned `From` calls, including `u32::from(u8/u16)`. The
[conversion fixture](../examples/rust-integer-conversions/README.md) verifies a
fixed accumulator wrap-boundary case and generic reference/field updates with
read/write authority and preserved neighbors. Conversion operands evaluate
once in order; casts truncate to sixteen bits and arithmetic checks that width.
This is not an arbitrary checksum proof. The Charon checkpoints subsequently cover tuple structs, shared array iteration
and indexed compound assignments. By-value aggregate operator operands and
crate extraction still block the unchanged adler2 loop.
Shared byte-slice `split_at` now supports two plain local tuple bindings,
full-width panic bounds, and an explicit signed-word pointer-offset limit.
Both slice lengths and reads through variable split points have regressions,
along with empty/endpoint splits, preserved full-width metadata, false claims,
missing read authority, and expanded-proof verification. Mutable splitting,
general tuple values, and range subscripts remain outstanding.
By-value array parameters/returns, non-byte slices, and crate extraction also
remain outstanding. Neither library is verified
by this assessment.

The Charon trial now imports resolved local `MulAssign<u32>`, `RemAssign<u32>`
and `AddAssign<&U32X4>` implementations through ordinary checked function calls.
The [operator checkpoint](../design/charon-trial/assignment-operators/operators.click)
keeps Adler2's multiplication and remainder bodies unchanged. Dispatch checks
core trait identity, local implementation identity and receiver/operand types;
proof names include the RHS type to distinguish overloads. There are no
operator-specific arithmetic axioms. A compiler regression checks two `AddAssign`
overloads with replacement semantics, alongside panic, authority, incorrect-lane
and expanded-proof rejection coverage.

The checkpoint now proves general unsigned multiplication with explicit
zero-or-safe lane premises, nonzero remainder, borrowed addition and symbolic
local two-call composition. Checked contradiction evidence, unsigned expression
reconstruction and indexed congruence preserve arithmetic obligations and memory
snapshots; scalar full-width boundaries and expanded proofs have separate
regressions. By-value aggregate operator operands and crate extraction remain migration work before
importing and proving the unchanged checksum loop. The default frontend is
unchanged.

## Milestone 1: experimental safe Rust

Support monomorphic functions over modeled integers and booleans, plain
structs, local initialization, branches, direct calls, `&`/`&mut` parameters,
and local reborrowing. Returning scalar or plain supported values is sufficient
initially. Use one pinned toolchain and target with an explicit overflow and
panic policy. Compiler acceptance alone does not prove absence of panics or a
functional postcondition.

The defining small regression is an unchanged Rust function over a two-field
struct. A helper reborrows one field, writes 7 through the child, then reuses
its parent to increment the field to 8. A caller proves that final value and
preservation of the other field. A shared-field case allows a disjoint write
while preserving the borrowed field. A non-`Copy` value move and disjoint
mutable field borrows supply companion resource regressions.

Pair positive verification with a false final-value claim, conflicting access,
use after move, stale child access, forged recovery, and duplicate recovery.
Distinguish source rejected by rustc from a functional claim rejected by Click.
Compiler rejection alone is not evidence that checked resource transitions
reject forged authority. Production-level negative tests must exercise the
actual selected transition rules rather than only the independent design model.

Acceptance:

- Ordinary Click verification imports unchanged `.rs` source and verifies the
  defining contracts through sidecars and the shared engine.
- All applicable negative cases fail at the documented compiler or checker
  boundary; the false functional claim reaches and fails Click's checker.
- Source attribution and actionable unsupported-feature diagnostics work;
  verify, profile, audit, and expansion agree wherever those tools apply.
  Expanded proof text verifies through the ordinary entry point.
- The supported subset, semantic flags, panic policy, trust assumptions, and
  a reproducible working example are documented. It is accurate to advertise
  experimental safe-Rust support without implying general Rust coverage.

## Milestone 2: unchanged Adler-32 implementations, one specification

The leading candidate pair is [zlib's C Adler-32 implementation](https://github.com/madler/zlib/blob/develop/adler32.c)
and Rust's [adler2](https://github.com/oyvindln/adler2). Pin exact revisions and
one supported configuration before implementation. This is selected Adler-32
coverage, not verification of zlib's compression algorithms or every adler2 API.
If source assessment finds a materially better pair, document the evidence and
replacement scope before changing this acceptance target; do not substitute a
fresh synthetic implementation and call it existing-library verification.

The inspected adler2 2.0.1 implementation uses chunk iterators, fixed arrays,
and custom arithmetic operators. Add slices, indexing, loops/invariants,
compiler-resolved method/operator calls, and the reachable library contracts
needed by the selected path. Generic library machinery may be instantiated
for this path without claiming general trait or generic support. Any assumed
library contract must be named in the trust boundary; the checksum computation
itself must be verified rather than assumed.

Define Adler-32 once over a logical byte sequence. Relate each implementation's
buffer/slice contents and accumulator representation to that shared definition.
Use explicit compatible initial-state and API preconditions so equality is not
asserted between different reset, seed, or null-buffer behaviors.

Acceptance:

- Both pinned implementations verify unchanged against the shared mathematical
  checksum specification for arbitrary finite inputs satisfying the contracts;
  selected configuration and API boundaries are explicit.
- Prove that input bytes remain unchanged, accesses are in bounds, arithmetic
  follows the specified semantics, Rust panic checks are unreachable, and the
  selected computations terminate.
- Prove incremental processing agrees with processing concatenated input,
  including empty inputs and chunk/remainder boundaries. Verify the optimized
  loops in the selected paths, not just a fixed-length or scalar replacement.
- Derive C/Rust result equality from their independently verified shared
  specification. Runtime differential tests are supplementary evidence.
- A false checksum postcondition is rejected. The fixture records original
  source identity and runs reproducibly in the normal verification gate.
- Publish a scoped demonstration: Click proves these selected C and Rust
  checksum implementations compute the same result under the stated contracts.

## Boundaries and delivery

Unsafe Rust, interior-mutability protocols, returned references, general
traits/generics, closures, async, threading, and broad standard-library
verification are outside this issue except for explicitly assessed compiler-
resolved library instances needed by the checksum path. A borrowing-focused
example remains alongside the checksum so resource compatibility has its own
acceptance evidence.

Submit coherent green increments through the fork PR workflow. Frontend import
and source fixtures can develop independently; coordinate changes to shared
kernel resources and execution. Follow the tooling-first policy in `AGENTS.md`:
reduce verifier/expansion/diagnostic failures before building more examples,
and do not route around them by changing the original programs. Representation
changes on hot paths require deterministic scaling regressions across multiple
sizes, including growing unrelated context. Run useful focused checks per
increment and the required gates; report their actual results.

Delete this issue and its list entry when both milestones, regressions, and
public documentation land. Retain architectural findings in the durable design
records so issue closure does not erase the supported boundaries.


### Charon cleanup and default-switch gate

The [live parity inventory](../design/charon-trial/parity.json) now enumerates
all legacy Rust example configs. CI re-extracts their unchanged source bodies
and checks unchanged sidecars, recording complete successes and explicit
extraction/proof gaps. Eleven of 16 fixtures verify unchanged (68.75%); all sixteen import (100%).
Five have proof-observation gaps. The required `test` gate also requires the existing live
Charon compiler and borrow-rejection suite. Locked checkpoints alone no longer
establish compiler compatibility.

A single compiled-in [Charon profile](../src/languages/rust/charon-profile.json)
now owns extraction pins, flags, and semantic interpretation versions, and the
build script reads it. The initial profile cleanup preserved lock identities. The subsequent
`shared-scalar-slice-length-v1` expansion deliberately versions interpretation
and updates checkpoint locks. Shared scalar array `.len()` now verifies the
unchanged `rust-arrays` fixture through compiler-resolved slice metadata;
`rust-array-values` now verifies its unchanged source and all sixteen contracts.
Whole-array reference assignments use the checked compact region path;
`external-scalar-array-snapshot-v1` adds immutable borrowed snapshots and writes.
Full read/write authority, read-only qualifiers, destination loans, alignment,
known bounds, and local initialization remain checked. Captured source runs and
sparse lanes preserve bytes independently after mutation without per-element
materialization; external copies/fills and kernel work are checked at
8/1024/million elements. Indexed source selection avoids unrelated parameter
cells. Heap/union storage and general symbolic pointer expressions remain
outside the compact path, and genuine by-value array parameters and aggregate
returns remain separate adapter gaps. Empty, signed, and million-element
length checks stay bounded and require no byte read authority. External Charon
locks need an explicit refresh. `split-shared-slice-while-header-v1` now imports
unchanged `rust-byte-sum` and `rust-loops`, preserving ordered header execution
on both true and final false tests. Single-entry header chains use pure scalar
copies, comparisons, and paired shared-slice metadata; calls, memory reads,
arithmetic, shared entries, and extra exits remain rejected. Header work and
emitted code have deterministic linear scaling coverage. All three unchanged
Rust loop bodies verify with loop selectors in a separate proof sidecar, but
the frozen numeric statement selectors still fail. Next provide stable proof
observations for these frontiers and legacy iterator state without generated
processed counts; also close tuple/slice return
shapes. Proof-adapted sidecars do not count as unchanged fixture parity.
The shared proof layout now indexes named ordinary assignments, local compound updates, and call-result
assignments for `execute_until(assignment(local, N))`. Source-local initialization
proofs survive unrelated compiler locals without counting helper statements.
Both syntax and typed-kernel paths retain checked forward execution, static
occurrence ordering, immutable sharing, and deterministic scaling regressions.
`loop(N)` still selects loop entry; `mark` names reached states. A final-store
selector does not precede its earlier right-hand-side helpers, and assignment
selectors are not snapshot expressions. This mechanism adds no generated ghost
state and does not close frozen numeric-selector or iterator-observation gaps;
fixture parity remains 10/16 (62.5%) and imports 15/16 (93.75%).
The layout also indexes `execute_until(read(N))`: the Nth statement containing
an explicit scalar memory load, before its checked execution. It excludes
address-only operations and implicit callee/aggregate reads, introduces no
permission or ghost state, and has linear construction and indexed-lookup
regressions in both layout paths. The full unchanged byte-sum source and
original prefix-sum contract now verify with loop, read, and assignment
selectors, including overflow, invariant preservation and termination.
The inventory records migrated proof sidecars separately and the live gate
verifies them after fresh extraction. AST comparisons preserve the original
contracts and pure specification definitions. Source-and-contract coverage
with these proof ports is 12/16 (75%); strict frozen-sidecar parity remains
10/16 (62.5%) and imports remain 15/16 (93.75%). Remaining proof work is stable
iterator observations and frozen numeric-selector compatibility; normalization
still needs tuple/slice returns in the fixed baseline, plus broader owned iterators.
The compiler-resolved `IntoIterator for &[T]` model now imports the original
`rust-iterators` body. It verifies trait/implementation identity, method linkage,
generic instantiation, scalar type and shared mutability; incoming i32/u32
slice parameters, ordinary source calls and reborrows preserve paired metadata.
Typed-read proofs cover empty/nonempty slices and forwarded metadata, with
false-claim, missing-view, forged declaration and metadata rejection coverage.
No processed count is generated. The frozen checksum proof still fails on its
legacy iterator observation name, so only import coverage increases this time:
14/16 to 15/16 (87.5% to 93.75%). Strict proof parity remains 10/16, and original
source/contract coverage with migrated proofs remains 12/16. `rust-split-at` is
the sole remaining baseline normalization gap; broader owned iterator support
and stable iterator proof observations remain later work.
Before switching the default, close every parity gap and retain stable proof
observations. Then retire the legacy exporter and its structured-body schema
path. Preserve qualified declaration identities before broader module/crate
imports; the current flat-name subset still rejects those shapes.

Compact external writes require a whole-footprint decision for existing possibly
aliasing runs. If separation cannot be checked compactly, they refuse promptly
rather than traversing the logical array extent.


### Charon shared byte split_at checkpoint

The adapter now imports the last rejected baseline fixture, `rust-split-at`,
and verifies its unchanged Rust source and all four frozen contracts/proofs.
Compiler-resolved shared byte splits retain the builtin tuple's two slice
values as explicit pointer/usize-length components, including projections,
complete copies/moves, replacement assignments, and storage ends. The existing
checked split semantics enforce panic bounds, memory-model offsets, and view
checks on byte reads. Empty input, endpoint splits, tuple copying/replacement,
forged declarations/projections, missing authority, false claims, tool
agreement, live re-extraction, and 8/128/1024 extent scaling are covered.

The fixed baseline now measures **16/16 imports (100%)**, **11/16 frozen
sidecars verified (68.75%)**, and **13/16 original sources/contracts verified
with the two existing proof ports (81.25%)**. Earlier checkpoint numbers above
are historical. Five frozen sidecars still need proof-interface migration;
three are iterator state observations and two have existing stable-frontier
proof ports. General tuple construction/boundaries, mutable/non-byte splits,
and the default switch/legacy retirement remain separate gates. Full fixture
import coverage does not mean the overall Charon migration is complete.

### Original chunks contract through Charon

The `design/charon-trial/chunk-proof` checkpoint now ports the original
`rust-chunks-exact` proof while retaining its Rust source and every contract
clause. It proves the remainder length and preservation of all input bytes
using actual imported iterator storage, without a generated processed count.
The preservation-only `execute_until(back_edge())` checks each crossed step
and rejects loop/function exits; invariant and ranking closure remain checked
separately. This removes cleanup statement counts from the migrated proof.

The fixed 16-fixture baseline is now 16/16 imports (100%), 11/16 frozen
proofs (68.75%), and 14/16 original sources/contracts with migrated proofs
(87.5%, up from 81.25%). The remaining two proof-port gaps are
`rust-iterators` and `rust-iter-references`. Frozen-sidecar compatibility,
default switching, and legacy retirement remain migration work.

### Original implicit byte iteration contract through Charon

The `design/charon-trial/iterator-proof/rust-iterators` checkpoint ports the
original `for &byte in bytes` sum proof with byte-identical Rust and the
unchanged mathematical sum contract. It observes real iterator cursor/remaining
state and source locals, uses named snapshots for preservation, and selects
loop entry, scalar read, total assignment, and back edge without MIR IDs or
numeric compiler statement counts. Signed addition overflow and iterator
termination remain checked; no generated processed count is restored.

The fixed baseline advances to 15/16 original sources/contracts verified with
four proof ports (93.75%, up from 87.5%). Imports remain 16/16 (100%) and frozen
sidecars remain 11/16 (68.75%). The remaining proof-port gap is
`rust-iter-references`; frozen-proof compatibility, the default switch, and
legacy retirement remain open.

### Original reference byte iteration contract through Charon

The `design/charon-trial/iterator-proof/rust-iter-references` checkpoint ports
the final original sum proof with byte-identical Rust and unchanged contract.
`let loaded_byte = step();` names the checked scalar assignment value, so
unnamed compiler temporaries require no MIR identifiers in the sidecar.
Bindings retain their checked value after the source local is overwritten or
leaves scope. The real cursor/remaining state, read access, signed addition,
mathematical prefix sum, and termination all remain checked. No generated
processed count or additional precondition is introduced.

The fixed baseline reaches 16/16 original sources/contracts verified with
five proof ports (100%, up from 93.75%). Imports remain 16/16 (100%); frozen
sidecars remain 11/16 (68.75%). No proof-port gaps remain in this baseline.
Default switching, frozen-sidecar compatibility policy, and retirement of the
legacy importer are still open migration gates, so this is not a claim that
the entire Charon migration is complete.

### Canonical native examples

The 11 canonical Rust examples whose frozen sidecars already verify under
Charon now select native extraction in their normal import configurations.
Rust source and proof text are unchanged; native ULLBC artifacts and genuine
refresh locks replace their locally generated legacy JSON inputs. The ordinary example
gate checks locked native inputs offline, and the required live gate continues
to freshly extract all 16 original sources and check contracts. CI archive
consumers therefore need no Charon compiler merely to verify an example.

Canonical adoption reaches 11/16 (68.75%), up from 0/16, using the same fixed
inventory. Imports and original source/contract proof coverage stay 16/16
(100%); frozen-sidecar compatibility stays 11/16 (68.75%). Next adopt the five
completed proof ports in the remaining canonical examples, then switch the
implicit backend default and retire legacy extraction. No claim of full
migration completion is made by this rollout measure.

### Complete canonical proof-port adoption

The remaining five canonical examples now select native Charon extraction and
their verified proof ports. Rust source and original contracts are unchanged.
Fresh ULLBC artifacts and locks support offline verification for all 16
examples. The archived original sidecars are pinned by SHA-256 in the parity
inventory, and legacy-backend regressions use those explicit archives.

The live gate independently checks all current canonical proofs and original
frozen outcomes after fresh extraction. Contract regressions compare canonical
ports with archived originals. Canonical adoption advances from 11/16 (68.75%)
to 16/16 (100%); imports and source/contract proof coverage remain 16/16 (100%).
Frozen-sidecar compatibility stays 11/16 (68.75%); the five literal old proofs
retain their recorded interface gaps rather than restoring generated names.
The implicit default switch and retirement of legacy extraction remain open.


### Retirement attempt: reproduced blockers

Canonical adoption remains 16/16 (100%), and the adoption PR has merged.
Switching the implicit default and deleting the legacy extractor requires
moving the remaining compiler-backed regressions onto native Charon inputs.
An attempted run of all 72 original `rust_*` integration tests through Charon
passed 48 and failed 24. Many failures are stale legacy artifact assertions,
frontier names, diagnostics, or old unsupported-feature expectations; they
must be ported with unchanged source/contracts and meaningful negative cases.
This run is diagnostic evidence, not a completed migration gate.

Two failures were independently reproduced through the ordinary native CLI:

- Deferred expansion used a dead compiler local. Automatic case selectors now
  retain their checked statement-entry snapshot, preserving existing `at` and
  `old` references and checking that the anchored condition has the same meaning.
  Nested case decisions are retained in outermost-first order. The unchanged
  native fixture passes isolated prepared expansion, retained-session audit,
  and whole-claim expansion; regressions also cover changed parameters and
  nested computed guards.
- Whole-array copy accepted an incomplete source view; this authority defect is
  now fixed with full physical-range checks for both source and destination.
  Kernel regressions cover partial permissions and compact work through one
  million elements. Locked native and freshly extracted unchanged Rust fixtures
  reject short source views, read-only destinations, and short destination owns.

Both independently reproduced blockers are now fixed. The attempted default,
extractor, and CI changes were restored to the previously green checkpoint;
no failing production switch is delivered. Port the original regressions and
only then remove the legacy build/runtime and implicit backend.
The remaining supported identity `From` case and test assumptions also need
review during that port; importing all 16 canonical fixtures alone does not
establish complete regression parity.


### Native backend retirement completed

The backend migration now has one path: schema-3 imports default to native
Charon, including all 16 canonical examples. Explicit `charon` and historical
`charon-trial` configurations use that same adapter. Schema 2 is rejected
before extraction; the legacy exporter, compiler/runtime pin, build scripts,
and CI archive have been removed. Pinned Charon and its driver replace them in
preparation and archive consumers. Every native lock is refreshed under the
versioned profile; ordinary verification still loads checked artifacts offline.

The original 72 regression responsibilities remain covered through native
artifacts or direct move/drop corruption checks. Ports preserve Rust sources
and contracts, use semantic loop frontiers and actual iterator state, and keep
false-result, panic, memory-authority, compiler-borrow, and expansion negatives.
Newly accepted patterns are proved instead of retaining obsolete rejection
expectations. Unsigned identity `From<T>` is resolved and signature-checked
under `unsigned-from-v2` alongside the existing widening conversions.
Borrowed iterator forwarding preserves one concrete state and checks resolved
standard declarations and associated-item signatures. Repeated extraction also
normalizes temporary output metadata, keeping shared-artifact locks reproducible.

Backend migration is complete (100% of the extraction, canonical adoption,
regression-port, default-switch, and legacy-retirement gates). General Rust
support and unchanged checksum-crate extraction remain separate feature work;
this issue stays open for those supported-subset and crate-boundary goals.

### Unchanged adler2 crate adapter trial

The [2026-10-06 trial](../design/charon-trial/adler2/README.md) preserves both
pinned adler2 2.0.1 source files byte-for-byte. Selected extraction with edition
2021, `std`, and the native optimized-MIR transforms succeeds: 15 bodies
including glue, with 94 blocks in `compute`. Production refresh stops before
checked lowering with `requires exactly one locked source file`; it publishes
neither artifact nor lock. A live regression records that boundary. This is
not a verified checksum or a successful crate import.

The next increment is a locked crate configuration and source closure, including
edition, features, and selected roots. Do not discover target files by crate
name alone: the extraction contains a different standard-library dependency
also named `adler2`. Preserve qualified declaration identities for modules,
inherent methods, and concrete trait implementations next; verify reachable
constructor and operator bodies rather than summarizing the checksum result.
Only after that adapter boundary passes should the unchanged implementation
be proved against the shared Adler-32 specification.

### Locked crate inputs and qualified declarations

Schema 4 now locks an explicit crate root, edition, features, selected roots,
and the complete compiler-observed file closure from rustc dep-info. Extraction
uses a private snapshot and rejects environment-dependent source macros,
escaping paths, symlinks, missing files, and extra inputs. All input bytes enter
the prepared identity, including modules with no translated body. Existing
schema-3 configurations and locks retain their one-file interpretation.

Module definitions and inherent methods use qualified, injective proof names;
call resolution keeps Charon declaration IDs. Assignment-operator implementations
retain their declaration/signature checks inside module namespaces. Positive
proofs cover same-named module functions and an inherent method call, with
false-claim and changed-input negatives.

The unchanged adler2 Rust-2021/std trial passes the former source-lock boundary
and reaches the concrete `Default` implementation. The next increment below
adds checked constructor bodies and record-return transport.

### Checked constructors and owned record returns

Schema-4 crate interpretation `click-charon-crate-v2` now resolves concrete
standard `Default` implementations by declaration, implementation, associated
item, signature, and diagnostic identity, then executes their actual bodies.
Ordinary constructors and forwarding wrappers return supported flat records
through the kernel aggregate-return interface. Live flags consume the return
place and initialize caller-owned storage exactly once; destructor cleanup
belongs to the caller. Existing schema-3 semantics and locks stay unchanged.

Regressions prove initialized fields through constructor calls and moves,
caller-supplied field values, changed constructor bodies, and a returned record
with `Drop`. The unchanged adler2 `Adler32::default` and `Adler32::new` bodies
now prove their two initialized fields. The complete `adler32_slice` extraction
next reaches unsupported by-value record assignment-operator operands
(`U32X4`). Support those concrete operands and their moves before continuing
the original computation and shared checksum proof; do not assume its result.

### Owned record parameters and operator operands

Schema-4 interpretation `click-charon-crate-v3` transports flat records by
value through kernel aggregate parameters. Callees receive fresh independent
storage, and checked call metadata distinguishes compiler moves from copies.
Moves consume the live source; copies require plain scalar/array fields and
no destructor, and retain a live source. Local copies use the same restrictions.
Destructor-bearing moved parameters follow the existing compiler Drop CFG.
Negative regressions cover missing or mismatched metadata, duplicate move
consumption, and forbidden copies. Existing schema-3 locks retain their
interpretation; older schema-4 crate envelopes require refresh.

At v3, the unchanged adler2 selection passed by-value U32X4 operator
registration and rejected its local constant/global initializer bodies. The
v4 increment below resolves that boundary without assuming the checksum
result or rewriting the crate.

Schema-4 interpretation `click-charon-crate-v4` imports named local scalar
constants with straight-line arithmetic initializer CFGs. Declaration, type,
source closure, initializer link, and qualified identity are checked; reads
use ordinary verified initializer contracts rather than assumed values or a
second evaluator. Frozen and live regressions cover duplicate module names,
`CHUNK_SIZE` arithmetic, full-width usize, narrow scalars, bool, false claims,
initializer deletion/overflow, changed source, forged reads, corrupt links,
statics, and cycles. Schema-3 semantics stay unchanged. Constant dependencies,
branching initializers, trait/generic constants, references and const-fn calls
remain later work. The unchanged selection rooted at `adler2::adler32_slice`
now produces and reloads a prepared import including `Adler32::compute`.
Its MOD and CHUNK_SIZE contracts prove 65521 and 22208. The helper increment
below proves the imported lane bodies. Next compose nested chunks/remainder
invariants with the shared checksum specification; checksum correctness
remains unproved.

### Original adler2 lane helper proofs

The locked full-crate fixture now proves the unchanged `U32X4::from`,
`AddAssign<Self>`, `RemAssign<u32>`, and `MulAssign<u32>` bodies, with all four
lane postconditions. Contracts retain the full safe u32 arithmetic domain:
signed 64-bit widening states addition guards, nonzero divisors protect
remainder, and quotient bounds permit multiplication including zero. Shared
byte views and receiver ownership protect reads and writes. Frozen/live source
hash checks and false-claim, short-read, missing-guard, and authority negatives
cover this boundary; verify/profile/audit and expanded certificates agree.
No Rust source or Charon interpretation profile changes were needed.

Next establish these helper preconditions from the original nested
chunks/remainder loop invariants, preserve byte accounting, and connect the
computation to the common Adler-32 specification. The checksum result and
whole-loop panic freedom remain unproved.


### Deferred-reduction lane ceilings

The adler2 bounds library now verifies the proposed lane ceilings
`A(n) = 65520 + 255*n` and
`B(n) = 65520 + 65520*n + 255*n*(n+1)/2` against the full u32 capacity.
Product and division certificates cover all batch indices through 5552;
`B(5552) = 4294690200` fits and `B(5553) = 4296171735` does not. Reduced
initial values satisfy the initial ceilings. The A-bound is preserved by a
byte update, and both next additions fit when the current lanes satisfy the
proposed bounds and `n < 5552`. Frozen helper and pure-bound claims verify in
the same prepared environment. False range, byte, endpoint, certificate, and
invariant-step claims are rejected, with checked tool expansion.

This proves arithmetic implications, not that the original loop maintains
them. The following increments prove the weighted B-bound recurrence and
bridge mathematical observations to native u32 checks. Next connect the batch
index to actual iterator state without a generated processed-count variable. Then
compose byte accounting with the shared Adler-32 specification. Total input
length is not restricted to one batch by these lemmas.


### Checked weighted lane recurrence

The bounds library now proves the triangular successor identity,
`B(n+1) = B(n) + A(n+1)`, and preservation of the weighted B-bound by
`b + (a + byte)` for every batch step `0 <= n < 5552`. It composes a bounded
Integer polynomial-identity certificate with a positive-constant quotient
shift under explicit nonnegative numerator and increment guards. Quotients,
machine values, and pure applications remain opaque to ring checking.
Mathematical Integer equalities can now rewrite the arithmetic spine through
the existing checked substitution routine. Forged coefficients, negative or
missing guards, wrong references/polarity, and false successor bounds are
rejected; work scales independently of unrelated premises and linearly in
certificate nodes. Expansion rechecks the new certificates.

Both lane-bound update implications are now established. Next connect those
invariants to the original nested chunks/remainder iterator state. The following
increment bridges Integer observations to native u32 guards. No generated processed-count
variable, Rust source edit, new import interpretation, checksum postcondition,
or whole-loop panic-freedom claim is introduced by this increment.


### Native u32 lane-step observations and guards

The bounds library now proves the widened `int64` guards required by the
original `U32X4::add_assign` body for both lane updates. Under the checked
A/B ceilings and byte bound, the native additions do not wrap, their unsigned
Integer observations equal the mathematical sums, and their observations
satisfy `A(n+1)` and `B(n+1)`. The B update uses the newly updated native A.
The library contains 18 theorem groups with 30 checked ensures clauses.

Two reusable checked kernel bridges require the mathematical sum to be at
most `u32::MAX`: one establishes the widened guard, the other the exact
unsigned addition observation. Unsigned definedness alone permits wrapping
and cannot replace that premise. Integer theorem arguments now capture explicit
machine observations through checked fixed-state evaluation, selecting only
referenced caller bindings; arithmetic evaluation guards remain kernel-checked. Heap observations use
logical specification read semantics and grant no access authority. Boundary models, altered declarations, wrapping/undefined
argument rejection, and deterministic local-selection scaling are covered.

Next establish these bounds over the original nested iterator states, then
compose the helper calls and byte accounting with the Adler-32 specification.
Whole-loop panic freedom and the checksum postcondition remain unproved.


### Lane index derived from remaining-byte state

The iterator bounds library defines the vector index from the existing native
remaining-byte state, using Integer observations and division by four.
Under `0 <= remaining <= total <= 22208`, the index lies in `0..5552`;
when at least four bytes remain it is at most 5551. Checked native subtraction
and nonnegative quotient-shift proofs establish that the four-byte transition
advances the index by one. The native A/B step proofs now preserve the lane
ceilings at the index observed after `remaining - 4`, and prove both native
addition guards using the index at the iterator head. No runtime processed
count is generated. The batch bound imposes no total input-length bound.

The new library has 14 theorem groups and 30 conclusions. Regressions cover
initial/empty input, short tails, exact multiples, full-batch endpoints,
missing remaining/length/definedness guards, false stride and successor claims,
and rejection of a larger batch. It imports the existing lane arithmetic;
the module graph also verifies with the pinned original helper contracts.
Tool checks retain all conclusions and recheck expanded certificates.

Next instantiate these conditional numeric and lane invariants over the
original nested Charon iterator loops, retaining shared byte views and proving
the helper call prerequisites. The original loop invariants, whole-loop panic
freedom, byte accounting, and checksum postcondition remain unproved.


### Integer equality evidence for iterator lemmas

The explicit citation rule now recognizes an Integer equality with its operands
swapped, matching the existing machine-equality rule. Theorem requirements,
citations, fixed-state rewrites, and fact transport retain checked operand and
polarity matching. Regressions reverify expanded certificates and reject missing
evidence, unequal observations, altered operands, and opposite conclusions.
This removes a proof-interface mismatch encountered while connecting the derived
iterator index; it does not establish the original nested-loop invariants.


### Original four-byte constructor range guarantees

The unchanged `U32X4::from` body now proves that each returned native u32 lane
is at most 255, alongside its existing exact byte correspondence. The guarantees
are available at the helper-call boundary with only the four-byte shared view
and length prerequisite. Regressions reject 254 as the universal bound for each
lane. This supplies the native byte range needed by the proposed lane invariants;
instantiating their Integer observations over the nested loops remains next.

### Unsigned order and constructor Integer bounds

Checked native-u32/Integer order bridges now preserve and reflect non-strict
order over the full unsigned domain. Their declarations require the exact
order premise, type, and conclusion. A proved library range theorem supplies
nonnegative observations through u32::MAX without assuming signed bounds or
no-wrap distribution. Boundary models exercise the sign-bit transition and
maximum; regressions reject missing/reversed guards, changed declarations,
false signed-range ceilings, wrapping distribution, and undefined arguments.

The unchanged original `U32X4::from` contract now exports all four byte lanes'
Integer bounds `0..255`, proved by applying those bridges to the returned
fields. False lower and upper bounds are rejected for each lane. The source,
locked Charon artifact, and import profile are unchanged. This connects the
constructor's guarantees to the numeric vocabulary used by the lane-step
lemmas. Next instantiate the original nested-loop invariants and establish
helper-call prerequisites from the stored iterator states. Whole-loop panic
freedom, byte accounting, and checksum correctness remain unproved.

### Original modulo-reduction lane ranges

The unchanged `U32X4::rem_assign` contract now proves, for each of its four
lanes, the exact original modulo result, native strict divisor bound, and
nonnegative Integer observation strictly below the divisor. A checked unsigned
remainder rule requires a nonzero divisor; a proved strict-order bridge uses
the existing checked non-strict reflection rule. Boundary models include zero
(excluded), one, MOD, the sign-bit transition, and u32::MAX. Regressions reject
missing/wrong divisor guards, altered declarations/types, and false tightened
native and Integer bounds for every lane. With MOD=65521 these guarantees give
the `0..65520` range required by the next batch's initial lane ceilings.

Original source, locked Charon artifact, and import profile remain unchanged.
Next instantiate the numeric invariants and helper-call prerequisites over the
original nested iterators, using the constructor's Integer byte bounds and
these modulo-reduction guarantees. Original loop preservation, whole-loop
panic freedom, byte accounting, and checksum correctness remain unproved.

### Original addition helper Integer interface

The unchanged `U32X4::add_assign` contract now accepts each lane's Integer
sum bound through u32::MAX, establishes the original widened overflow guard,
and exports both exact native and exact Integer sums plus nonnegative updated
observations. This connects the helper call to the lane recurrence vocabulary;
the sidecar does not assume distribution over wrapping addition. Regressions
reject a missing lane guard, MAX+1, a tautological wrapping guard, changed
ownership, and false Integer sums and lower bounds on every lane. Original
source, artifact, and import profile are unchanged. The original nested-loop
invariants, whole-loop panic freedom, byte accounting, and checksum correctness
still need proofs.

### Restricted closers at the original computation's exit

An original `Adler32::compute` proof experiment exposed that top-level
`simp() using { ... }` was not retained after function exit. A minimal C
reproduction incorrectly blamed an earlier valid `have` as unsupported.
The ordered outcome driver now retains the restricted closer, checks only
its listed proposition premises on each returned outcome, and uses the same
checked resource transition and certificate capture as ordinary `simp`.
Regressions cover missing/false/irrelevant premises, both return paths,
grouped ownership and value guarantees, and independent expansion rechecks.
This repairs proof tooling; it does not prove the original nested loops or
checksum contract. Original Rust sources and extraction locks are unchanged.


### Bounded snapshot premise reconstruction at the original loop frontier

An empty-input `Adler32::compute` experiment reached the original lane-summing
loops, but a smart `have b == 0u32` repeatedly reconstructed old premises after
its deadline. Snapshot candidate lookup now seeks lazily in the persistent
tree instead of collecting and sorting every recorded state. Traversal,
candidate matching, and cross-snapshot operand reconstruction respect sticky
work/deadline exhaustion; the enclosing closer reports that budget error
before starting another fallback. Multi-size regressions cover ordering,
tombstones, logarithmic near-anchor work, exact lowering, and cancellation.
The original failing trial now unwinds at its enforced bound. This is a
verifier repair, not an empty-input or nested-loop proof. Next decompose the
original computation's scalar/modulo checkpoint into explicit checked steps,
then establish the existing lane ceilings over the stored nested iterators.
Original Rust sources, extraction locks, and the import profile are unchanged.


### Original computation empty-input boundary

The locked adler2 sidecar now verifies the unchanged `Adler32::compute` body
on empty input from the constructor state `a = 1`, `b = 0`, proving both final
fields and all executed access/panic prerequisites. Its scalar zero survives
the original addition and modulo. Checked operand snapshots cover lane
recombination, both ordered four-lane summation loops, final modulo values,
and u16 stores; no source counter or assumed invariant is added. The helper
and constant getter bodies are checked with the boundary contract. A few
native adapter capture names remain explicit proof anchors for the frozen
import; adapter changes must recheck them.

Ordinary regressions reject missing empty-input, initial scalar B, and state
ownership prerequisites. The full boundary proof, false output/initial A
rejections, and verify/profile/audit/expansion agreement are nightly checks.
Contract parsing also recognizes the existing narrow scalar casts, using the
existing C conversion rules; boundary, false-value, and missing-definedness
regressions cover them. Original source files, extraction locks, and the
import profile are unchanged.

Next establish the existing lane ceilings over the original stored nested
iterators for nonempty chunks and tails. General initial-state preservation,
nonempty byte accounting, whole-loop panic freedom, and full checksum
correctness remain unproved.

### Original computation single-byte boundary

The unchanged `Adler32::compute` body now has a checked contract for one
arbitrary byte from `a = 1`, `b = 0`. The serial iterator's actual read is tied
to the original input, both additions have checked overflow bounds, the input
byte is preserved, and both final field observations equal their native modulo
expressions: `(1 + byte) % MOD` and `(6 * MOD + 1 + byte) % MOD`. These give
the single-byte checksum values without wrapping. The proof retains original
adapter operand snapshots and introduces no source counter or assumed invariant.

The contract fragment shares the canonical helper/getter contracts through the
fixture harness, which checks all seven bodies; the existing empty-input
sidecar is retained. Function-contract imports between sidecars remain outside
the import delivery. Kernel cast-identity certificates now recognize canonical
nested conversions and exact unsigned byte-readback masks, retaining explicit
destination bounds. A separate execution-driver repair admits `execute_until`
inside proof-case arms and succeeds when the requested frontier is already
current. Minimal C and expansion regressions cover that repair.

Missing length/view and empty-input rejection are ordinary checks. Complete
single-byte verification, false checksum/input-preservation claims, and proof
tool agreement run nightly. Original Rust sources, extraction locks, artifact,
and import profile are unchanged. The serial-tail extension below covers two
and three bytes; derived lane ceilings over the original stored nested
iterators remain later work. General initial states, nonempty vector batches, whole-loop
panic freedom, and the common full checksum specification remain unproved.


### Original computation two- and three-byte tails

The unchanged `Adler32::compute` body now has checked constructor-state
contracts for arbitrary inputs of length two and three. Together with the
existing empty and single-byte boundaries, this covers each possible serial
remainder length before the first four-byte vector path. Each original read
is tied to its input index, and explicit facts check the stored cursor and
remaining count after every read. There are no new source locals, generated
processed counts, or assumed loop invariants.

The proofs establish the original A/B recurrences from the lane-recombination
state `A = 1`, `B = 6 * MOD`, check both overflow guards on each pass, preserve
every input byte, and prove both final native modulo expressions through the
original `u16` stores. The A ceilings are 256, 511, and 766; the B ceilings are
393382, 393893, and 394659. The canonical helper/getter contracts are reused
and all seven bodies checked for each fragment.

Ordinary regressions reject missing length/view, an incorrect extent, and
an incorrect constructor state. Nightly tests check the complete positive
proofs, false A/B outputs, false preservation of every byte, swapped byte
weights in B, repeated preceding-byte reads, and verify/profile/audit/expansion
agreement. Original Rust sources, artifacts, locks, and import profile are
unchanged.

### Copying local scalar arrays after checked calls

The first nonempty vector path exposed a kernel copy defect at the original
`b_vec += a_vec` call: its by-value operand copies `a_vec` after a checked helper
has updated it. Initialized local storage was rejected when that call had
discarded cached lane values. Such copies now capture the current immutable
memory snapshot for unknown lanes, preserving represented lanes and the existing
initialization, type, alignment, bounds, and authority checks.

`design/charon-trial/copy-after-call` contains a reduced, frozen Charon crate
with both bodies checked: mutate a local array through a helper, copy it, mutate
the source again, and return the independently captured post-call value. False
pre-call/later values and insufficient or read-only authority are rejected.
Kernel regressions cover partial havoc, invalid storage, and deterministic
compact-copy scaling through a million elements. Proof-tool regressions recheck
verification, profiling, expansion, and nightly audit. The original `adler2`
sources, artifacts, locks, and import profile remain unchanged; its complete
four-byte checksum contract is still unproved.

### Exact observations of the original lane multiplication

The unchanged `U32X4::mul_assign` body now proves exact Integer products for all
four lanes, alongside its native products and unsigned observation bounds. The
checked `uint32_mul_to_integer` bridge requires the original native quotient
guard, including the zero multiplier case. It does not infer mathematical
non-wrapping multiplication from native expression definedness.

This supplies the missing observation interface for carrying derived lane
ceilings through vector recombination. A checked surface theorem derives the
262080 ceiling for a reduced lane multiplied by four. Kernel regressions compare
the emitted guard and product observation with independent unsigned boundary
models, including zero factors, values above the signed sign bit, and both sides
of the last safe quotient. Original helper regressions reject false products,
false lower/upper bounds, and missing overflow guards for each lane. Original
Rust sources, artifacts, locks, and import profile remain unchanged; the complete
four-byte computation contract is still unproved.

Concrete zero-factor theorem applications also exposed eager evaluation of an
unused right disjunct. If that right side cannot lower, the kernel now preserves
an exactly known true left path with its facts and obligations. When both sides
lower it retains the written disjunction, including its choice-certificate shape.
Unknown or false left sides retain the existing lowering. Independent theorem
regressions reject undefined right sides when needed and false conclusions;
expansion independently rechecks the resulting certificates.

The unsigned-bound certificate rendering bug found by the four-byte investigation
is fixed. A final addition over sign-bit-flipped unsigned atoms now uses the
goal's source comparison instead of wrapping machine sums; the unchanged checker
requires that comparison to encode the exact child sum. Regressions verify and
independently recheck expanded upper and lower bounds on both sides of the sign
bit, and reject insufficient bounds, unlisted premises, and forged certificates.
The observed-product identity rewrite bug from that investigation is also fixed.
Checked Integer substitution now folds multiplication by zero and one just as
lowering does, retaining the goal's independently checked source presentation.
It preserves shared symbolic products instead of multiplying arbitrary-size
literals. Regressions cover both operand orders, full-width unsigned
observations, pure proofs, execution `have` scopes, and function outcomes;
expanded certificates reject missing evidence and false or altered products.
Deterministic rewrite visit counts remain linear across shared product depths.
The checked symbolic zero-factor theorem now proves the product equals zero after
the native multiplication bridge and Integer observation rewrites. The checked
multiplication ceiling example uses arithmetic for its native quotient guard.
Both arithmetic tooling bugs are resolved; the complete original four-byte
computation remains unproved.

### Exact preservation through lane reduction

The checked `uint32_remainder_of_lt` rule now proves `value % divisor == value`
from the strict native unsigned bound `value < divisor`. That bound excludes
zero divisors and works across the full unsigned range, including values above
the signed sign bit. Exact standard-library declarations and independently
rechecked expansion reject missing or weakened guards and altered conclusions.
A byte-lane execution fixture connects native reduction to exact Integer
observations for values at most 255.

The unchanged original `U32X4::rem_assign` contract now exports preservation for
each lane when its incoming value is below the divisor. Its original nonzero
divisor requirement and unconditional remainder/range guarantees remain in
place. Per-lane regressions reject a non-strict guard, changed byte value, and
cross-lane substitution. Rust source and the locked Charon artifact are unchanged.
This supplies the exact lane identity needed after reduction on the first
four-byte path; the complete original four-byte computation remains unproved.

Next prove the first nonempty four-byte vector path and establish/preserve the
derived lane ceilings over the original stored nested iterators. General
initial states, nonempty vector batches beyond that boundary, whole-loop panic
freedom, and the common full checksum specification remain unproved.
