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

The arithmetic prerequisite also delivers signed scalar parameters/returns,
64-bit locals and modular captures, checked signed `+`, `-`, `*`, `/`, `%`,
negation and comparisons, explicit promotions, C++20 signed narrowing, and
integer-to-Boolean conversion. Unchanged upstream `operator-=` is verified
for distinct objects under half-range bounds and for self-aliasing across the
entire signed range. A modular source caller frames unrelated memory.

The `signed-arithmetic` fixture preserves Bitcoin's quotient/remainder
correction expression with a signed 64-bit dividend and checks fourteen
concrete rounding/boundary cases, both directions and signs, exact division,
and signed extrema. It proves general quotient/remainder contracts and checks
expansion, retained audit, hostile claims, zero divisors, and signed overflow.
The shared kernel now discharges positive-divisor guards and bounded signed
64-bit multiplication, folds signed wide arithmetic through indexed equalities,
and handles self-subtraction. Regressions cover lazy evaluation of undefined
constant division and fixed query work across unrelated fact populations.
These arithmetic prerequisites do not prove the general rounding theorem or
the upstream `__int128` path. The next milestone below remains open.

Unsigned scalar support now delivers by-value 32/64-bit parameters, returns,
locals and modular captures, wrapping arithmetic, comparisons, division/remainder
and the supported mixed conversions. C++20 uint64-to-int64 conversion now
preserves all source bits through a distinct kernel cast mode, with sign-bit
and extrema regressions, arbitrary-input round trips, modular caller framing,
and following signed overflow checks. Ordinary C conversion behavior is retained.
Unsigned references and record fields are outside this slice. The unsigned
fast-path fixture preserves both fee expressions but returns the intermediate,
so it is not a proof of upstream `EvaluateFee`.

The unchanged `GetSizeOfCompactSize` in the pinned `serialize.h` is proved for
all uint64 inputs in four disjoint ranges (encoded lengths 1, 3, 5, 9). Its
`sizeof` and static constexpr `numeric_limits::max()` calls are pinned-Clang
compiler constants with retained source spans and locked input closure.
Ordinary verification, expansion/reverification, retained audit and hostile
length claims agree. Full-width unsigned constant bounds use the queried
endpoint's index, with fixed-work regressions over unrelated fact populations.
This establishes encoded length, not byte serialization or parsing.

Concrete function templates are now imported through ordinary selected callers.
Boolean value arguments and the supported unqualified builtin scalar type
arguments have distinct Clang identities and sidecar names, including equal-width
`long`/`long long` distinctions. Pinned Clang selects `if constexpr` in constant
evaluation context; the artifact retains the selected arm, constant condition,
and source spans. Selected unsupported behavior fails explicitly. Regressions
cover modular callers, receiver ownership, framing, false contracts, type
identity, Boolean substitution, absent else arms, and rejection of unsupported
arguments and dependent selection. Both instantiated unsigned fee fast-path
expressions verify concrete rounding cases, expansion and retained audit. These
are synthetic prerequisites; no additional upstream fee proof is claimed.

Direct return calls now support matching signed/unsigned 32/64-bit and Boolean
results, including implicit `this` calls to concrete method template instances.
The synthetic `FeeFrac` fast-path wrappers preserve Bitcoin's direct
`return EvaluateFee<...>(at_size)` form. Regressions prove modular scalar
forwarding, branches, caller framing, typed capture before normal destruction,
and object-free exception propagation, with selected-caller expansion and audit.
Call graph and cleanup validation remain explicit. Uncaught return-call cleanup
edges have structural coverage; guarded `try` returns and resource-bearing
exceptional contracts remain outside this slice.

Nested scalar calls now support one call argument in a direct free-function
return call, including deeper chains and multiple stable scalar siblings.
By-value scalar parameters/locals, literals, locked constants, and supported
integer/Boolean casts are stable and total, so all argument orders agree even
when the inner call writes memory or throws. Memory-reading siblings, arithmetic,
multiple nested calls, and sibling side effects remain explicit errors. Typed
captures preserve normal cleanup and inner exceptions skip outer calls.
Regressions cover widths/signedness, Boolean results, each argument position,
casts, source-name collisions, mixed-width branches, hostile claims, and
selected-caller expansion and audit. Name allocation and argument lowering have
deterministic scaling regressions. The synthetic 64-bit fee fixture preserves
`Div(Mul(...), divisor, round_down)` and proves concrete positive/negative rounding
and exact division, including concrete Boolean template wrappers; zero divisors
and unproved product bounds are rejected.
This does not yet import Bitcoin's wide helper path or field-reading siblings.

Static scalar helpers now retain class and declaration identity without an
implicit receiver or importing unrelated object layouts. Ordinary
`Class::helper` selection, class-qualified/unqualified calls, and reachable
concrete template instances support the existing scalar call positions,
including stable nested arguments. The synthetic static `Mul`/`Div` rounding
fixture verifies both signs through Boolean template wrappers, expansion and
audit. Scalar-type, distinct-class, initializer, exception, false-claim, and
artifact regressions are covered. Object-qualified calls and pointer/reference
signatures remain rejected. Bitcoin's wide path, `Assume`, and field-reading
siblings still require further support.

Scalar call evaluation now uses one normalization path: explicit evaluation
statements followed by a typed value. Return and integer-local initializer
wrappers retain their source role, but nested calls and their ordering checks
are shared with discarded calls. Supported nested initializers no longer need
source rewriting into return calls. Returns still capture before destruction;
exceptional evaluations use the existing active cleanup edges. Ambiguous sibling
reads/effects remain rejected in every context.

C++ now prepares execution, contract-facing signatures, explicit layouts, and
local-object metadata within its frontend. C++ and Rust supply the same
prepared execution package to the shared verifier. The verifier no longer
traverses C++ bodies or translates C++ types. Original typed artifacts,
load source identities, and locked compiler/source identities remain attached
to the prepared input. The plain C parser already supplies the same signature
and layout vocabulary; its lazy translation-unit path remains intact.

Lifetime cleanup is now derived from typed declaration/record identities and
one scoped construction stack, independently of the artifact's exit lists.
Validation and lowering use the same lifetime events: successful construction,
lexical exit, return, and unwinding to a catch boundary. Returns before any
construction and between two constructions have unchanged-source regressions;
normal return capture, reverse destruction, conditional/sibling scopes, and
scalar exception fixtures retain their behavior. No per-branch live-environment
clone or scan of a final return's cleanup list is needed. Deterministic tests
cover growing event and cleanup-edge counts. Existing semantic-profile limits
remain for the validity/profile/budget cleanup below. Partial construction,
temporaries, copy/move, broader scope arrangements, and wider exceptions are
future lifetime events/admissions, rather than additional lowering paths.

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

## Next work: finish the design consolidation

Complete these design steps before extending the Bitcoin fee arithmetic slice.
Each should be a coherent change with unchanged-source regressions, hostile
artifacts and false claims, verification/expansion/audit agreement, and
multi-size deterministic work checks for affected hot paths.

1. **Scalar interpretation before wide arithmetic.** Consolidate scalar type
   interpretation and conversions across the artifact validator, kernel
   lowering, and contract-facing interfaces. Specify widths, signedness,
   promotions, narrowing, Boolean conversions, overflow and division
   definedness against the pinned target. Reuse shared C/Rust operations where
   semantics agree and keep language-specific policies explicit. Add
   `__int128` only after its execution, contract types, and proof obligations
   fit that design; do not introduce another isolated family of matches.

The inventory validity/profile/budget slice is delivered. The single-record and
leaf-plus-dependent constant shape caps are replaced by named declaration
budgets (256 records, 1,024 constants, and 1,024 functions). Constant forests
retain the existing initializer semantics and checked evaluation agreement.
Record layouts retain the existing field/ABI semantics and require distinct
proof-facing names. Unused layouts now fail structural graph validation.
Lowering builds record and constant indexes once and shares them across all
functions. Serialized nesting/containers are bounded before deserialization,
and call depth uses cached full subgraph depths so traversal order cannot hide
an exhausted limit. Multi-size constant/record/function regressions cover the
new inventories; malformed dependencies, duplicates, bad evaluated values,
orphan layouts, and budget boundaries remain rejected.

Scope validation now uses a lexical environment whose children borrow their
parent and own only newly declared places and names. Entering a normal scope or
catch handler neither clones outer types nor scans all outer names. Catch names
belong to the handler environment. Multi-size deterministic regressions check
shared outer storage, local-only entry counts, sibling isolation, duplicate
identities, shadowing, and forged references. The existing lifetime combinations
remain constrained by their semantic profile; lifetime inventory counts use
the named budgets described below.

Graph place indexing is delivered. Each visited function builds one index of
borrowed declaration IDs and places, including parameters, locals, and catch
bindings across blocks and branches. Reference arguments and destructor edges
use indexed type lookup. Duplicate IDs anywhere in a function are structural
errors, including reuse across disjoint sibling scopes; equal readable names
with distinct IDs remain valid. Lexical environments still establish visibility
and lifetime checks still establish cleanup order. Deterministic regressions
cover growing parameters, locals, and reference edges without repeated body
searches, plus malformed IDs. Source regressions verify, expand, and audit
reference-call proofs with growing unrelated places and reject false claims.
Lifetime inventory budgets are delivered: each function allows up to 1,024
local declarations, including catch bindings, and 256 cleanup scopes. Exporter
and checker count independently, including both branch arms. Larger inventories
of top-level destructible objects, sibling scopes, and objects within a supported
scope share the existing construction stack and reverse cleanup checks.
Multi-size regressions cover prefix returns, cleanup order, validation/lowering
work, proofs, expansion, audit, malformed exit lists, and atomic budget failures.
The three-scope restore proof records restoration at each boundary with explicit
steps; its C++ source is unchanged. Multiple trivial aggregates, deeper scopes,
overlapping outer/sibling combinations, and the existing conditional/exception
arrangement restrictions remain semantic-profile limitations. Artifact schema 34
requires an explicit refresh of earlier locks.

Recursive function metadata validity is delivered in its own module. Before a
function's semantic profile is checked, a borrowed traversal validates every
statement, expression, initializer, argument, cleanup, and type-alias chain,
including both branch arms and nested scopes/handlers that the current profile
will reject. Declaration metadata, source spans, and alias provenance/cycles
are structural checks; supported widths, operand relationships, lexical
visibility, and lifetime arrangements remain semantic checks. The existing
serialized nesting budget bounds recursive input. Local semantic validators
reuse the metadata helpers when checked in isolation. Regressions mutate every
span and identity in a corpus covering all recursive variants, distinguish
malformed metadata from unsupported nested lifetimes, and measure growing
syntax/alias work without cloning lexical environments. Artifact schema remains
34 and existing supported-source proofs remain unchanged.

Next consolidate scalar interpretation before wide arithmetic.

Resolved function identities and contract names are delivered. One immutable
ID-to-name index drives kernel definitions, every call (including construction
and cleanup), load owners, and proof interfaces. Unique readable names remain
unchanged; free namespace names flatten `::` to `_`. Colliding spellings use
`__click_cpp_decl_` followed by the full hexadecimal UTF-8 declaration ID.
That prefix is reserved, including for user declarations, so encoded names are
injective without digest assumptions or order-dependent numbering. Anonymous
namespace spellings also use encoded names. Nested namespace selectors work. The original
artifact IDs remain independently available, and `contract_name(id)` exposes
the binding on the lowered import. Regressions cover reachable overloads with
`long`/`long long` parameters of equal width, namespace/global spelling collisions,
and same-named static helpers in different namespaces. Selected overloads still
require a future signature selector; namespaced method selection and same-named
record layouts remain outside this slice. Existing template instance names remain
readable when unique. Hostile reference-name/ID mismatches still fail validation.

The expression normalizer and prepared execution boundary are delivered in
this consolidation. Future expression positions and richer ordering support
must extend the same normalizer. In particular, calls inside arithmetic,
conditions, assignments, and constructor arguments remain outside this slice;
integer local initialization, return calls, and discarded calls share the
current stable-sibling policy.

## Next bounded milestone: fee arithmetic

Select unchanged `FeeFrac::EvaluateFeeDown/Up` and their instantiated helpers
from this pinned release. State input bounds that make the result representable
and prove the documented rounding direction, including negative fees, exact
division, and a nonzero remainder. Concrete Boolean template instances and `if constexpr` now have prerequisite
coverage. The unsigned-to-signed-64 conversion prerequisite is also delivered:
the synthetic fast paths now preserve the signed return and concrete rounding
cases. The selected upstream source still requires `__int128`,
assumption obligations, and argument-order support for field-reading siblings
in `Div(Mul(...), size, RoundDown)` on this target. Stable scalar sibling arguments
are now supported; upstream `EvaluateFee` is not yet supported.

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
