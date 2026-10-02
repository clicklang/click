# P2: Extend C++ support toward Bitcoin Core

The long-term goal is to verify substantial parts of unchanged Bitcoin Core.
Grow support through independently useful, bounded proofs that exercise the
common execution and resource model. Each delivered slice must state exactly
which source, properties, compiler profile, and dependencies it covers.
Importing C++ syntax or proving one helper does not establish verification of
Bitcoin Core as a whole.

## Delivered baseline and current gap

The [basic C++ example](../examples/basic-cpp/README.md) verifies reference
aliasing, selected local objects, constructors/destructors, normal cleanup,
and a direct modular caller. The [control-flow issue](control-flow.md) records
the delivered bounded scalar-exception and conditional-lifetime cases, and
owns broader cleanup/unwind work.

The [Bitcoin Core integration](../integrations/bitcoin-core-money-range/README.md)
already verifies the unchanged `MoneyRange` from v31.1, commit
`9be056a8a72b624dae9623b2f7bded92c2a21c91`, through its real Clang compilation
command. Its hermetic input closure includes `src/util/feefrac.h`,
`src/policy/feerate.cpp`, and `src/span.h`; these provide concrete next targets
without guessing what this Bitcoin release contains.

The first value-method milestone is delivered in this change: ordinary
methods, const record references, mixed signed 64/32-bit fields, same-width
field addition, and signed integer equality. The upstream
[`FeeFracIsEmpty.click`](../integrations/bitcoin-core-money-range/FeeFracIsEmpty.click)
proves exactly `size == 0` while preserving both fields.
[`FeeFracAdd.click`](../integrations/bitcoin-core-money-range/FeeFracAdd.click)
and [`FeeFracAddSelf.click`](../integrations/bitcoin-core-money-range/FeeFracAddSelf.click)
prove exact sums for distinct and self-aliasing objects under sufficient
half-range overflow bounds. The synthetic `value-methods` compiler-import
fixture also proves modular source callers and frames unrelated caller memory.
It checks expansion and retained audit sessions, false claims, missing field
authority, and missing overflow bounds. Artifact tests reject receiver
qualification mismatches, const writes, const-to-mutable calls, and mixed-width
addition. The existing Bitcoin archive and project flags remain unchanged.

## Required invariant

Every accepted selected C++ operation must have faithful, checked execution
semantics: receiver identity, field ownership, aliasing, integer definedness,
lifetime, and all accepted outcomes must survive import and lowering.
Unsupported reachable behavior must fail explicitly. Like
[rust-support.md](rust-support.md), use one proof language and one bounded
verification engine. Keep the compiler/translator trust boundary explicit and
share existing kernel operations where their semantics agree; a separate
C++ verifier or a wholesale renaming of C-prefixed kernel types is not a
prerequisite. Unselected declarations
in a project header must not force verification of an entire class or standard
library, but their layouts and other semantically relevant information must
still be validated. Preserve unchanged upstream source as the integration
regression for every new slice.

## Next bounded milestone: fee arithmetic

Select unchanged `FeeFrac::EvaluateFeeDown/Up` and their instantiated helpers
from this pinned release. State input bounds that make the result representable
and prove the documented rounding direction, including negative fees, exact
division, and a nonzero remainder. The selected source uses templated
`EvaluateFee`, `if constexpr`, signed/unsigned arithmetic and conversion,
division/remainder, and `__int128` helpers on this target. Those are further
importer and arithmetic-model work; the delivered method slice does not yet
support them.

Before implementing the upstream proof, freeze a small regression that
preserves the chosen rounding/conversion pattern. Include hostile false
rounding claims, zero divisors, unproved overflow or narrowing bounds, and
unsupported reachable behavior. Acceptance requires the unchanged source
proof and modular callers, explicit compiler/library assumptions, ordinary
verification agreeing with expansion/reverification and audit, documentation
of the precise supported profile, and `scripts/check.sh`. Add deterministic
multi-size scaling regressions if the work changes a verifier hot path.

## Follow-up direction

These are candidate slices, not claims that their dependencies are supported
or a requirement to implement the entire list in one change. Choose the
next unchanged source and exact contract before implementation; update this issue to retain only remaining open work.

| Slice | Candidate and useful claim | Concepts it forces |
| --- | --- | --- |
| Fee arithmetic | `FeeFrac::EvaluateFeeDown/Up`: correct rounding and no undefined arithmetic under stated input bounds. | Compiler-resolved template instances, `if constexpr`, signed/unsigned conversions, division/remainder, and the selected target's wide integer path. |
| Bounded bytes and serialization | Select one unchanged span/cursor or serialization helper; prove bounds, consumed/produced length, and byte meaning or round trip. | C++ loops, array/range authority, representation and endianness, returned references, and explicit malformed-input behavior. |
| Owning containers | Select one bounded operation of Bitcoin's `prevector`; prove content preservation and ownership on each accepted outcome. | Allocation, object initialization, copy/move, destruction, small-buffer transitions, and iterator/reference invalidation. |
| Larger Bitcoin subsystem | Choose a bounded script, transaction, or validation component and state its safety and functional claims separately. | Composition of verified helpers, explicit external/library contracts, and domain specifications beyond language support. |

Fee rounding is nearby but materially harder than `IsEmpty`: in this pinned
profile `FeeFrac::Mul`/`Div` select `__int128`, and `CFeeRate` uses the inherited
`FeePerUnit` template wrapper. Do not replace these with the fallback path or
change project flags to avoid wide integers or inheritance. Establish the
individual arithmetic contracts first. Bitcoin's `Assume` annotations must
be exposed as contract obligations or explicit assumptions, not silently
counted as proved checks.

For spans, object-copying a view must not duplicate pointee ownership; returned
references must stay tied to the backing object's live storage. For containers,
prove exactly which operations invalidate old views, and reject their later
use. A modular library contract must declare whether its implementation is
verified or assumed, and pin the relevant implementation/profile. Resolving
a template instance is not itself a proof of the library it calls.

## Shared work and deferred coverage

Reuse the existing common resource and arithmetic machinery where its semantics
agree with C++. Coordinate mathematical division support with
[mathematical integers](../docs/internals/mathematical-integers.md), byte
reasoning with the [byte-representation design](../docs/internals/byte-representation.md),
and lifetime/aliasing investigations with
[supporting-more-languages.md](../design/supporting-more-languages.md).
C++ references can alias; do not impose Rust's exclusive-borrow rules on them.

Broader unwinding belongs to [control-flow.md](control-flow.md); concurrency
and atomics belong to [concurrency-and-atomics.md](concurrency-and-atomics.md).
Virtual dispatch, general inheritance/subobject identity, RTTI, arbitrary
standard-library verification, full exception semantics, and cross-target
coverage are deferred until a selected proof requires a precise slice.

Preserve upstream C++ just as existing C is preserved: adaptation belongs in
the importer, execution model, sidecar contracts, and proof tools. Tooling
instability blocks milestone work under `AGENTS.md`; do not work around it
with altered source, irrelevant proof bookkeeping, or larger search budgets.
