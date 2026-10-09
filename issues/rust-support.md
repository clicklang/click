# P1: Support safe Rust and verify a shared C/Rust checksum specification

## Goal and scope

Deliver a useful, explicitly bounded safe-Rust verification path through Click
sidecars and the shared checked engine. Verify selected unchanged Rust and C
Adler-32 implementations against one mathematical specification, then derive
result equality under matched input and state conditions. This is P1; the Linux
rbtree remains the key launch demo.

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

The unchanged pinned adler2 2.0.1 selection imports successfully. Constructors,
constants, lane helper bodies, numeric ceilings, and lane preservation verify.
The original computation has a terminating whole-body bounds proof for every
multiple-of-four length up to 22,204 bytes from any canonical initial state.
It carries all eight lane ceilings, the shared input view, and actual iterator
state through reductions, recombination, scalar sums, and final 16-bit stores.
Both output fields remain below 65,521. Checked partition lemmas relate full-width
lengths, signed indices, four-byte prefixes, and zero-to-three-byte tails.
Full outer batches, short-tail loop induction, and checksum correctness remain
incomplete.

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

### 1. Prove arbitrary-length Adler loop invariants

Compose the existing initialization, helper-call prerequisites, and
lane-preservation lemmas into induction over the original stored inner iterators
and outer batches. Preserve memory views, lane ceilings, byte order and byte
accounting through reduction/reset and all remainder paths. Establish general
initial-state preconditions and termination using actual iterator state.

Acceptance:

- Arbitrary admissible lengths, empty inputs, exact boundaries, multiple outer
  batches, and short tails satisfy the original loop invariants.
- Original checked accesses and arithmetic are justified at every iteration;
  whole-loop panic freedom follows from the proof.
- False bounds, stale cursor/remaining claims, missing authority, wrong byte
  order, and incorrect reduction/reset steps are rejected.

### 2. Verify Rust against the common checksum specification

Define Adler-32 over a logical byte sequence once, following
[the checksum assessment](../design/rust-checksum-assessment.md). Relate the
original optimized lane state, reductions, and packed result to that definition.
Prove arbitrary finite input correctness under the explicit supported memory
range and API preconditions, including compatible initial states.

Acceptance:

- The unchanged selected Rust computation terminates, preserves input bytes,
  cannot panic, and returns the specified checksum.
- Incremental processing equals processing concatenated input, including
  empty and chunk/remainder boundaries.
- A false checksum postcondition fails. No assumed library summary supplies
  the checksum computation's postcondition.

### 3. Verify C and publish the shared demonstration

Pin the selected configuration and revision of
[zlib's Adler-32](https://github.com/madler/zlib/blob/develop/adler32.c), verify
its unchanged optimized path against the same specification, and derive C/Rust
result equality. Match seed/reset and null-buffer behavior explicitly.

Acceptance:

- Both implementations independently satisfy the shared specification for
  arbitrary inputs covered by their contracts; accesses, arithmetic, byte
  preservation, termination, and incremental processing are proved.
- Result equality follows from those proofs. Differential runtime tests are
  supplementary evidence.
- Publish reproducible locked fixtures and a scoped demonstration. Keep slow
  whole-proof checks nightly and bounded regressions in the normal gate.

### 4. Close experimental-support architecture requirements

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
models, and relevant dependencies. The current signed-word memory-range limit
must remain explicit without truncating full-width Rust metadata.

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
