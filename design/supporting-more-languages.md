# Supporting C, C++ and Rust

Click uses one specification language and checked engine for its supported
C, C++ and Rust subsets. The languages have equal standing; the historical
"C++ first, Rust next" sequence is not a current priority rule. Launch scope
and open delivery requirements are owned by the
[roadmap](../roadmap/README.md), including [Rust support](../roadmap/rust-support.md).

## Shared engine, language-specific admission

Frontends share proof objects, logical terms, immutable memory snapshots,
resources, execution and tool orchestration wherever semantics agree.
Each frontend retains its own rules for valid values, object creation,
aliasing, moves, lifetime, cleanup and exceptional outcomes. A parser accepting
a source extension is not evidence that those operations are supported.

Use pinned compiler semantic information: Clang declaration/type/layout and
cleanup evidence for C++, Charon's selected rustc MIR representation for Rust,
and the admitted C import profile. Bind compiler/extractor identity, options,
target/layout, selected source/dependencies and library assumptions into
prepared inputs. Reject partial or mismatched artifacts. Keep original source
bytes and source metadata for contracts, observations and diagnostics.

Compiler extraction and source-to-kernel translation belong to the trusted
boundary. Rust's type/borrow checking establishes source legality; it does not
prove functional postconditions or authenticate arbitrary sidecar authority.
Adopting Charon does not adopt Aeneas's functional memory interpretation.

## Authority, values and cleanup

Access mode, transfer role and snapshot are distinct. `owns` at a call borrows
and returns authority; `consumes`/`produces` can describe a move. `views` is a
stable shared loan backed by suspended write authority. An old observation
stays a fact about its snapshot, not necessarily the current value.

A mutable reborrow cannot duplicate ownership. Recovery must return updated
contents once, preserve disjoint access, and reject expired or wrong child
identities. Field partition and nested dependencies need explicit evidence.
The [production Rust assessment](rust-borrow-authority-assessment.md) owns the
implemented call and local-lease subsets; the independent
[worked correspondence](rust-resource-correspondence.md) and
[compiler probes](borrow-probes/README.md) are evidence for their stated models,
not substitutes for imported source or adversarial sidecar checks.

Do not apply stable read-only payload rules to interior-mutability types such
as `Cell`, `RefCell` or `Mutex`. Each needs its own sharing protocol.
Returned borrows, unsafe raw access, `Pin`, partial initialization, atomics and
escaping authority need their selected semantic boundaries.

Implicit cleanup must use resolved source operations in source order across
normal, early and admitted exceptional exits. C cleanup jumps, C++ destructors
and Rust drops can share machinery without acquiring each other's semantics.
The selected two-guard/conditional-lifetime C++ control-flow demonstration is
complete; broader exceptions, replacement and unwinding remain separately
scoped. [Aggregate construction](aggregate-construction.md) and
[Object-model laws](cpp-object-model.md) record the destination, copy and
lifetime distinctions to preserve.

## Evidence required for a new slice

Select a real source witness and preserve its program. State the compiler,
target, configuration and trusted library/runtime assumptions. Check actual
bodies and modular calls, false postconditions, absent authority, invalid
operations and hostile artifact metadata. Ordinary verification, profiling,
expansion, cold and retained checking must agree on the claim.

Keep repeated values and shared CFG joins compact. An operation's work must
follow its selected input and relevant state delta, with deterministic
multi-size checks for changed representations/hot paths. A successful
compiler probe, small standalone resource model or faster corpus timing does
not establish the whole semantic or scaling boundary.

Concurrency is an independent test of the resource model. The modeled shared
counter and one-shot release/acquire publication demonstrations are complete;
Linux RCU, broader memory orders and real platform/runtime bindings remain
separate requirements in [Concurrency](../roadmap/concurrency-and-atomics.md).
The [compiler/ABI item](../roadmap/multiple-compilers.md) owns additional targets.

## History

The [original language-sequencing investigation](https://github.com/clicklang/click/blob/2175760b9/design/supporting-more-languages.md)
retains the compiler comparisons and original support-slice proposals.
Current interfaces and limits live in the [C reference](../docs/reference/language/c.md),
[Rust reference](../docs/reference/rust.md), and
[coverage matrix](../docs/reference/coverage.md), rather than that old sequence.
