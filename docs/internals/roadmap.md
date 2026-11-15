# Roadmap

Click's launch strategy is to finish P1, verify the Linux kernel rbtree
implementation within the agreed minimum viable rbtree (MVR) scope, and launch
with that proof as the key demo. The
[roadmap index](https://github.com/clicklang/click/blob/master/roadmap/README.md)
is authoritative for priorities and scope. This page does not duplicate its
feature list or maintain a second proof-status ledger.

## Complete the P1 work

Choose work by dependencies and what it unblocks; P1 means required before
launch, not a fixed execution order. The selected stable-view, basic C++,
concurrency, representation-copy, cleanup and shared-heap demonstrations have
landed with bounded support claims. They are evidence for those slices, not
unfinished launch milestones or general language completeness.

The current Rust host/dependency requirements and proof-tooling boundaries
remain in the roadmap. The former Linux-only Rust launch ruling and the
historical "C++ first, Rust next" sequence do not override it. C, C++ and Rust
have equal standing in the public support claim.

Verifier correctness and tooling stability precede feature work. A false
acceptance, broken expansion, unusable diagnostic or slow simple checker is a
blocker even if rbtree does not expose it. Follow
[proof-failure triage](../concepts/proof-failure-triage.md) and
[verification efficiency](verification-efficiency.md). Close a milestone only
when its implementation, relevant regressions and documentation land.

## Current rbtree status

The [rbtree milestone](https://github.com/clicklang/click/blob/master/roadmap/rbtree-example.md)
owns current proof progress and acceptance. Use its current witnesses and
existing defect reports, rather than treating an older sidecar count or an
implemented representation repair as evidence that an entire proof passes.
The [current object-model audit](https://github.com/clicklang/click/blob/master/design/object-model-current-audit.md)
likewise distinguishes selected passing mechanisms from remaining composition
checks. That audit is bounded evidence, not a full-corpus verdict.

MVR requires the agreed unchanged pinned source and public inline boundary,
sequential memory safety and defined behavior, tree and red-black invariants,
exact node/in-order preservation, traversal, termination and modular
augmentation callbacks. The roadmap defines the compiler/target and any
explicit source/runtime assumptions. Passing copied helper bodies or individual
case proofs does not establish the whole pinned implementation.

Completion requires the full agreed proof and the required repository checks.
The proof must not be promoted to concurrent RCU correctness or verification
of the entire Linux kernel. [Trust](../concepts/trust.md) describes the shared
compiler, translation and external-assumption boundary.

## Launch and later work

Publish reproducible pinned sources, configuration, sidecars and verification
instructions. State exactly what is proved, under which target and assumptions,
and use that result in the launch demonstration. Broader language, compiler,
concurrency and object-lifetime coverage follows the P2 items and subsequent
explicit priorities; it is not implied by the bounded launch demonstrations.

The [historical launch note](https://github.com/clicklang/click/blob/2175760b9/docs/internals/roadmap.md)
retains the October 13 per-case counts and copied-header limitations. Those
counts were already superseded by general proof consolidation and later
regressions, so they must not be presented as current status.
