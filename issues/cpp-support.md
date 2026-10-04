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
when the inner call writes memory or throws. Aliasing memory-reading siblings, arithmetic,
multiple nested calls, and sibling side effects remain explicit errors. Typed
captures preserve normal cleanup and inner exceptions skip outer calls.
Regressions cover widths/signedness, Boolean results, each argument position,
casts, source-name collisions, mixed-width branches, hostile claims, and
selected-caller expansion and audit. Name allocation and argument lowering have
deterministic scaling regressions. The synthetic 64-bit fee fixture preserves
`Div(Mul(...), divisor, round_down)` and proves concrete positive/negative rounding
and exact division, including concrete Boolean template wrappers; zero divisors
and unproved product bounds are rejected.
The scalar-isolated field-reading sibling extension is described below; Bitcoin's
wide helper path remains unsupported.

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

Checked compiler-assumption obligations are delivered. A direct
`__builtin_assume` statement is identified by Clang's builtin declaration and
lowered to a labeled assertion in the common kernel. Its condition must be
proved at the site, never silently trusted. Because the builtin does not
evaluate its operand, supported conditions are total scalar predicates over
by-value parameters/locals and locked constants, with supported casts,
comparisons, and conjunction. Memory reads, runtime calls, arithmetic, and
side effects remain rejected. Offline regressions cover missing/false
conditions, conditional execution, constant reachability, normal destruction,
expansion/reverification, retained audit, forged artifacts, and growing statement
inventories. Ordinary user-named `Assume` calls remain ordinary calls. This is
the obligation mechanism prerequisite; Bitcoin's library `Assume` macro still
needs separate support. Artifact schema is now 36 and earlier locks require
an explicit refresh. The unchanged Bitcoin fee source remains unsupported.

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

## Delivered design consolidation

The planned cleanup steps are delivered. Continue with the fee arithmetic
milestone above, preserving unchanged-source proofs, hostile-artifact and false
claim rejection, verification/expansion/audit agreement, and deterministic work
bounds. Wider arithmetic must extend the shared scalar model and common kernel,
including execution types, contract types, and definedness obligations.

Scalar interpretation now uses one descriptor for the pinned target's Boolean
and signed/unsigned 32/64-bit value kinds, with qualification kept separate.
The validator, execution lowering, and contract interfaces share classification,
scalar type comparisons, and checked literal interpretation. One conversion
policy selects shared kernel casts and the explicit C++20 signed-bit cases;
Clang retains promotions and usual arithmetic conversions as typed nodes.
Arithmetic still uses the common kernel: signed overflow is undefined,
unsigned arithmetic wraps, division truncates toward zero, and division/remainder
require nonzero divisors and exclude the signed minimum/-1 pair. Reference and
field restrictions stay position-specific. New boundary tests check scalar
qualification, unsupported widths, and literal ranges. Offline source proofs
cover Boolean widening and uint64-to-int64 bit preservation, including expansion,
retained audit, and false claims. Existing arithmetic/proof fixtures are unchanged;
artifact schema is now 36. `__int128` remains a feature prerequisite for the
full fee arithmetic milestone, rather than another isolated family of type matches.

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
arrangement restrictions remain semantic-profile limitations. Artifact schema 36
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
36 and existing supported-source proofs remain unchanged.

Next extend the shared scalar and kernel design for the fee arithmetic milestone.

Field-reading siblings beside a scalar-isolated nested call are delivered.
The producer and offline checker require that nested call's inputs to be scalar
values, with no pointer/reference inputs or further input calls. Mutable globals
and external calls remain rejected, so the call cannot access caller storage.
The shared normalizer snapshots field siblings before the call, checking read
authority even when the call throws. Aliasing and hidden input calls remain
rejected; general alias analysis and other memory-reading siblings are deferred.
Offline proofs cover every argument position, supported field casts, initializer
and discarded contexts, concrete positive/negative and exact/remainder fee
rounding in a synthetic method/template/static-helper wrapper, expansion,
reverification, and retained audit. Hostile checks cover missing authority, false
results, direct/hidden aliases, and unchecked reads before exceptions. Argument
inventories have deterministic validation/lowering scaling regressions. This
does not yet admit the unchanged Bitcoin wide arithmetic/Assume source.

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
cases. The selected upstream source still requires `__int128`
and support for its library `Assume` annotation on this target. Stable scalar
and isolated field-reading sibling arguments in `Div(Mul(...), size, RoundDown)`
are now supported; upstream `EvaluateFee` is not yet supported.

The shared exact multiplication-range prerequisite is delivered. An explicit
`integer_product_bounds` certificate checks the four corner products of two
constant-bounded mathematical Integer operands. A checked lemma proves that
a signed 64-by-32-bit product fits the signed 128-bit range; machine values
compose through their separate `to_integer` observers. Hostile certificates,
large constants, deterministic scaling, expansion/reverification, profiling,
and retained audit have coverage. This is shared proof arithmetic available to
C, Rust, and C++; it does not yet execute native `__int128`.

The shared fixed-width constant and conversion layer is delivered. Formats
record signedness and 8–128-bit width; private checked payloads preserve the
full signed and unsigned 128-bit ranges. Checked numeric conversion and explicit
modulo conversion have distinct APIs, with exhaustive small-value and exact
wide-endpoint oracle tests. Existing machine bounds, Integer observations and
reverse conversions, rewrite normalization, and C++ literals/constant casts
use this layer. Runtime bridges require an exact format match. General
source-level `__int128` execution remains unsupported; the bounded kernel
wide scalar profile below admits only the listed operations, without frontend
admission.

The shared runtime now has an explicit modulo cast boundary for existing
8–64-bit integer values. C++20 and Rust select the same symbolic conversion
policy; constant conversions use the shared checked payloads. Width,
signedness, and operand definedness remain explicit. Narrow signed carriers
are sign-extended, and cast construction stays local to the operand root.
Ordinary C narrowing and checked Integer conversions retain their separate
rules. This removes frontend mask/cast sequences before extending widths.

The bounded shared wide scalar runtime is delivered: typed 128-bit literals
and variables, scalar locals and function parameters/results, substitution,
16-byte scalar size/alignment under the pinned profile, and exact Integer
observations. Reverse Integer conversions retain both wide range obligations;
truthiness observes all bits. Legacy arithmetic carriers are refused;
native arithmetic and typed memory access are admitted only in the slices below.
C0 identities carry the kernel types without adding source parser admission.

Symbolic wide widening, narrowing, and signedness changes are delivered at
the shared explicit modulo boundary. Cast terms retain both machine types;
constant substitution preserves every bit and sign extension. Ordinary C
wide signed conversions retain representability obligations. Exact Integer
observation preserves numeric widening, while value-changing casts remain
typed machine observations. Root construction and validation stay bounded,
including large operands; source admission remains open.

Checked signed 128-bit multiplication is delivered. Exact operand observations
feed a shared Integer product; both native range guards must hold before the
shared checked machine conversion produces the typed result. Unknown bounds
retain both signed-overflow paths. Existing 64-by-32 product-bounds certificates
discharge the guards without admitting unproved native definedness. Boundary
oracles, earlier operand undefined behavior, narrow operand promotion, function
results, specification capture, and indexed work scaling are covered.
Unsigned wrapping multiplication and other native wide operations remain open.

Exact typed 16-byte memory cells are delivered through the shared typed-load
and typed-store operations. Signed and unsigned load kinds preserve their
checked formats; symbolic reads retain snapshot identity and certified defining
facts. Full-width extents, initialization, and resource authority remain
required. Framing and store invalidation include the high eight bytes, and the
conservative unknown-width bound is sixteen. Generated store sequences include
wide cells and compare indexed gap skipping with the complete reference path;
load/validation work is tested over multiple unrelated-memory sizes.
Byte reinterpretation and source admission remain open.

Shared wide object pointers, pointer slots, fixed scalar arrays, and arrays of
wide pointers are delivered, with exact internal C0 type identities. Element
strides and scalar alignment are sixteen bytes; pointer objects and slots
remain eight bytes under LP64. Address-of, indexing, and local declarations use
the shared paths. Regression coverage includes full-width payloads, one-past
and uninitialized reads, separate slot/pointee authority, startup versus
ordinary-entry initializer authority, and symbolic storage scaling through one
million elements. Compact narrow-array copies reject overlapping wide cells.
Source spellings, wide byte reinterpretation, and wide callbacks remain open.

Next add frontend source admission,
retaining the source's resolved machine semantics. Use the shared formats and
conversion policies rather than inventing a C++-specific numeric carrier.
Then cover wide truncating division/remainder and checked narrowing
for the unchanged `FeeFrac::Mul`/`Div` path. Keep mathematical Integer semantics
separate, especially its planned Euclidean division. The library `Assume`
annotation remains an explicit contract/assumption boundary to resolve before
the upstream fee proof.

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
