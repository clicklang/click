# P1: Support safe Rust and verify a shared C/Rust checksum specification

Priority: P1.

Soundness: incomplete. Language coverage. Unsupported Rust is refused. The
pinned Charon front end is a documented trusted dependency.

## Goal and scope

Deliver a useful, explicitly bounded safe-Rust verification path through Click
sidecars and the shared checked engine. Verify selected unchanged Rust and C
Adler-32 implementations against one mathematical specification, then derive
result equality under matched input and state conditions. This is P1; the Linux
rbtree remains the key launch demo.

The implemented shared construction/return-destination contract is recorded in
[aggregate construction](../design/aggregate-construction.md). It preserves
existing Rust aggregate return, initialization and move/drop protocols. The
checksum milestones below can continue with their current semantics; they are not blocked on that design.

Experimental Rust support and the checksum demonstration are independently
reviewable milestones. Document and ship the supported subset without waiting
for the full library proof. Neither milestone implies general Rust coverage.

## Current capabilities and evidence

The Charon migration is complete. Native Charon is the sole extraction path;
canonical examples and compiler-backed regressions use it, and the legacy
exporter and toolchain have been retired. No HIR/MIR frontend migration remains.
Ordinary verification loads locked artifacts offline through the shared engine.

Supported operations include checked scalar arithmetic, branches, direct calls,
shared/mutable references and local reborrows, supported records and move/drop
protocols, compact scalar arrays and snapshot copies, byte slices, splitting,
and stored shared iterators with actual cursor/remaining state. Crate imports
lock roots, edition, features, target, qualified declarations, and the complete
compiler-observed source closure. Concrete constructors, record returns and
parameters, and selected resolved operators execute verified imported bodies.

The unchanged pinned adler2 2.0.1 selection imports successfully. Its original
`Adler32::compute` body now proves both final fields equal the common checksum
specification on the entry input snapshot, for every length zero through
2,147,483,647 bytes from any canonical initial state. It terminates, preserves
input bytes, checks every native access and arithmetic guard, and stores both
fields below 65,521. The proof follows actual full-width cursor and remaining
state through full batches, the aligned remainder, scalar accumulation and the
final tail. Checked signed observations impose the explicit proof range limit;
no generated processed counter or assumed checksum summary supplies the result.

Checked helper bodies and lane-state lemmas connect the actual constructor
bytes, four-byte recurrences, deferred B seed contributions, reductions and
ordered recombination to the shared mathematical specification. Full-range
native-count and byte-position bridges preserve exact values and addresses.
The specification independently proves concatenation and incremental equality
for A, B and the packed checksum under explicit signed-range split bounds and
canonical A seeds. Implementation-level incremental composition remains pending.

Constructors, one- through four-byte computations, and the shared checksum
getter verify. The getter proves exact packing for any two u16 fields and has a
checked bridge from field specifications to the packed specification. The
unchanged `adler32_slice` entry point composes the checked constructor, general
computation and getter for every length zero through 2,147,483,647, returns the
common packed checksum, and preserves every input byte. `write_slice` accepts
any canonical initial state and returns canonical fields satisfying the common
A/B specification. Logical byte-index guards are bridged explicitly to native
64-bit range membership. The specialized empty call needs no byte authority.

The independently locked, unchanged zlib one-byte path proves its packed result
equal the same specification and preserves its input byte; its empty path also
verifies. General-length C correctness and C/Rust result equality remain pending.

Full original-computation smart audits exhaust the standard ten-minute run
bound before completing a site, while ordinary verification succeeds. Continue
with ordinary verification and retain audits where they complete; the audit
timeout supplies no proof verdict. Standalone native-count and chunk-position
claims pass complete audits. Whole-body correctness, false final A/B claims,
and larger proof-tool checks run nightly.

Composition regressions cover record and scalar-array storage starts, shared
chunk-view transport, and all four returned/copied vector lanes across local
stores. Automatic scope exits retire construction ownership. Negative tests
reject missing input authority, noncanonical seeds, and false induction or
final bounds. Whole-proof verification and tool agreement run nightly.

Detailed support boundaries and reproducible commands belong in
[the Rust reference](../docs/reference/rust.md). Current checksum evidence lives
in [the Adler trial](../design/charon-trial/adler2/README.md). Keep this issue a
current roadmap: replace status when work lands rather than append checkpoints.

## Remaining work, in delivery order

### 1. Compose Rust incremental processing

Use the [shared Adler-32 specification](../design/adler32-spec.click), following
[the checksum assessment](../design/rust-checksum-assessment.md). Compose the
general public update contract across repeated calls and connect it to the
checked mathematical incremental equality.
Prove arbitrary finite input correctness under the explicit supported memory
range and API preconditions, including compatible initial states.

Acceptance:

- The unchanged Rust public entry point composes checked bodies, terminates,
  preserves input bytes, cannot panic, and returns the specified packed checksum.
- Incremental processing equals processing concatenated input, including
  empty and chunk/remainder boundaries.
- A false checksum postcondition fails. No assumed library summary supplies
  the checksum computation's postcondition.

### 2. Verify C and publish the shared demonstration

Pin the selected configuration and revision of
[zlib's Adler-32](https://github.com/madler/zlib/blob/develop/adler32.c), verify
its unchanged optimized path against the same specification, and derive C/Rust
result equality. Match seed/reset and null-buffer behavior explicitly.

The [unchanged pinned zlib trial](../design/charon-trial/zlib/README.md) imports
all selected bodies and proves the canonical empty-input and one-byte cases
offline; the one-byte result satisfies the shared specification and preserves
the byte. Its null reset path verifies for any seed and nonunit length.
Expression updates preserve consumed values, loop exit-side effects, native
unsigned wrap, and checked pointer strides; nested `DO16` blocks also import.
Connect the original nonempty computation to the common specification, then
prove compatible seed/reset/null-buffer behavior and incremental processing.

Acceptance:

- Both implementations independently satisfy the shared specification for
  arbitrary inputs covered by their contracts; accesses, arithmetic, byte
  preservation, termination, and incremental processing are proved.
- Result equality follows from those proofs. Differential runtime tests are
  supplementary evidence.
- Publish reproducible locked fixtures and a scoped demonstration. Keep slow
  whole-proof checks nightly and bounded regressions in the normal gate.

### 3. Close experimental-support architecture requirements

Resolve these requirements alongside the library proof; do not postpone them
behind new language coverage:

- **Borrow authority:** connect explicit exclusive-child suspension/recovery
  to production resource transitions. Compiler borrow rejection alone does not
  establish rejection of forged sidecar authority. Test stale child access,
  forged/duplicate recovery, disjoint field borrowing, and parent reuse.
- **Stable proof observations:** provide source-facing slice, array, and
  iterator observations so contracts need not depend on compiler temporary
  names or storage details. Preserve qualified identities, shadowing, source
  spans, snapshot meaning, and expanded-proof correspondence.
- **Consistent library models:** consolidate supported resolved instances and
  document their preconditions, effects, panic behavior, and named trust
  assumptions. Validate declarations/signatures and bind model versions into
  prepared identities; lookalike methods must not acquire models by spelling.
- **Composition and scale:** keep one semantic execution path, shared CFG joins,
  compact repeated initialization/copies, and checked cleanup on supported
  exits. Combine references, arrays, arithmetic, iterators, owned records and
  drops in regressions. Verify/profile/expansion/audit must agree where applicable.

Assess each item against current production evidence before adding mechanisms;
retain existing working representations where they already meet acceptance.
The experimental milestone closes when its defining borrowing/move regressions,
production negative tests, proof-tool agreement, and accurate public support
and trust documentation satisfy these requirements.

## Semantic boundaries and delivery rules

rustc establishes source typing and borrow legality. Click checks functional
claims and supplied memory authority; references grant no allocation or
deallocation authority. Keep allocation lifetime, access authority, and value
validity distinct. Lock source, compiler/exporter, target/layout, semantic flags,
models, and relevant dependencies. Preserve full-width Rust metadata and range
endpoints. Proofs using signed index observations, including the current checksum
trial, must state and check their narrower range explicitly.

Unsafe Rust, interior mutability, returned references, general traits/generics,
closures, async, threading, heap support, mutable/adapted iterators, and broad
standard-library verification are outside this issue unless a concrete instance
needed for the selected checksum path is explicitly assessed.

Keep original Rust and C sources unchanged when developing proofs. Repair
lowering, resource rules, contracts or proof tooling instead of making source
more verifier-friendly. Reproduce and fix tooling defects before extending
examples; retain meaningful negative tests and deterministic scaling checks.
Deliver coherent green increments through the fork PR and merge queue workflow.
Delete this issue and its list entry when both milestones and documentation land.

Durable design references: [resource correspondence](../design/rust-resource-correspondence.md),
[Charon assessment](../design/rust-charon-assessment.md),
[adapter trial](../design/charon-trial/README.md),
[language design](../design/supporting-more-languages.md), and
[stable views](../docs/internals/stable-views.md).
