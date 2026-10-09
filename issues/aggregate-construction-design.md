# P2: Shared aggregate construction and return destinations

## Goal and invariant

Represent construction, copying and object lifetime explicitly in the shared
checked engine. A frontend must select the operation justified by its imported
language semantics. Constructing into a destination preserves that object's
identity; copying an existing aggregate preserves its field values, including
pointer values. Neither operation invents pointee authority or extends another
allocation's lifetime.

The shared constructor path already accepts an explicit destination. Existing
source frontends materialize aggregate returns as field copies into caller-visible storage.
That is not a general implementation of C++ returned construction: a constructor
can observe its object's address or store a pointer to one of its fields. An
extra copy can change the relationship between that pointer and the result
object. The unsupported C++ cases remain refused; this is a design gap, not a
claim that the currently admitted profile accepts an incorrect construction.

The chosen direction is to extend shared destination construction through
returns and temporaries, rather than requiring every admitted constructor to
be address-independent. Keep the existing allocation, layout, initialization,
resource and lifetime machinery. C and Rust retain their current source
semantics while C++ adopts the additional capability.

## Current foundation

- Shared `DeclareAggregate`, construction declarations and `CopyAggregate`
  already distinguish fresh storage from field copying.
- C, Rust and C++ use the shared aggregate-return layout interface. Rust also
  uses construction declarations with its existing move/drop and initialization
  protocol; changing return handling must preserve that protocol.
- C++ int32 field addresses follow checked nominal projections, preserve
  effective const qualification and check storage without reading field values.
- Existing offline regressions in [cpp_import.rs](../tests/cpp_import.rs)
  distinguish constructor identity from copying, exercise address formation
  before initialization, and reject missing write authority, false claims and
  forged const qualification.

The implemented return materializer and symbolic call result live in
[functions.rs](../src/kernel/functions.rs); shared function interfaces live in
[contracts.rs](../src/kernel/primitives/contracts.rs). Preserve the existing
construction/copy distinction in both body and modular execution.

## Small intended regressions

Use this identity-sensitive class as the starting example:

```cpp
struct Node {
    int* self;
    int value;
    explicit Node(int input) noexcept : self(&value), value(input) {}
};
```

Direct construction of a local `Node node(input)` must establish
`node.self == &node.value` and allow a later read through `node.self` under the
object's existing authority. Forming the address before `value` is initialized
must not read the unwritten value. The source regression is already implemented
as `constructor_destination_preserves_pointer_to_its_own_field_offline`.

Copying a live `Node` into another object must retain the original self-pointer,
rather than rebase it to the destination field. This is already covered by
`record_copy_keeps_self_pointer_value_without_rebasing_it`.

Shared-kernel regressions now cover a constructor populating a supplied return
destination, forwarding it through two factories, and copying a temporary before
retiring it. They distinguish dead self-pointers from live external backing.
Surface typed-frontend regressions also cover ordinary, expanded and retained
verification of the native self-pointer contract. The remaining work is source
admission and C++ expression-lifetime lowering, not another kernel interface.

Only then admit corresponding unchanged C++ factory/caller source. For example,
`return Node(input)` must follow the selected language/compiler profile's actual
construction and permitted copy rules. Do not assert a universal self-pointer
identity for every trivially copyable returned class: required prvalue
construction, optional named return elision and permitted trivial-class
parameter/result temporaries must be distinguished. Keep cases refused while
that evidence or their checked transitions are missing.

## Design work and delivery order

1. Specify destination identity, initialization state, result binding and
   lifetime in the shared call/contract interface. Identify how ordinary
   execution, modular calls and checked proof objects represent the same
   transition. A caller-provided destination is not automatically fresh or
   distinct from arguments and other caller storage.
2. Implement checked construction into result storage and destination
   forwarding. Preserve field-copy returns as an explicit existing operation.
   Complete initialization must be proved before a value can be observed;
   exposing an address grants no extra read or write permission.
3. Represent temporary materialization and retirement at the correct boundary.
   Keep descriptor storage separate from the backing allocations to which its
   pointer fields refer. Copying or retiring a descriptor must not retire those
   independently live allocations.
4. Admit a bounded C++ source profile using Clang's resolved expression
   categories, constructors, copy operations and compiler/ABI evidence. Account
   for every admitted execution instead of selecting an elision silently.
5. Verify unchanged pinned `std::span<int>` returned construction and complete
   the `SpanPopBack` target in [cpp-support.md](cpp-support.md). Keep the existing
   native reference contracts, uint64 extent and accepted single-range bound.

The accepted interface direction, Surface Click boundary, initialization and
lifetime obligations, and staged implementation contract are recorded in
[the aggregate construction design](../design/aggregate-construction.md).
The shared kernel now supports complete-object destination returns, including
body execution and body-certified summaries forwarded through two factories.
The hidden result binding grants no storage or ownership; actual writes must
initialize the modeled value fields. Surface contracts now supply and certify the
implicit result-storage resource while preserving native signatures and field
addresses. Typed-frontend regressions cover forwarding, expansion, retained
verification and required initialization. Existing C/Rust copy returns are
unchanged.
Ordinary void constructors now bind an explicit destination parameter and
complete its initialized fields through body-certified summaries, including
aligned subobjects without resizing their parent allocation. Constructor proof
entries describe an unwritten footprint without fixing the parent's extent.
C++ local construction uses raw storage and explicit embedded constructor calls,
while the shared lifetime-end statement covers
temporary retirement. Bounded C++ returned construction, forwarding and new-object
initialization now select the shared construction mode. Their typed constructors
and value helpers must satisfy the copy-equivalence restriction below; direct
local constructors retain the existing address-sensitive profile. Assignment
from these calls materializes a distinct RHS object, copies into the live LHS
and retires the RHS at the full-expression boundary.
The precise compiler/ABI evidence is an admission gate for each new C++ return
shape; the design does not treat a Clang expression category as sufficient
evidence of copy elision.

## Implementation progress after handoff

The returned-construction increment implements steps 1 and 2 below, plus
initialization of a new object from a construction-return call. Schema 51 records
these operations explicitly. Constructor/helper eligibility is recomputed from
validated bodies and memoized by declaration identity; no serialized flag
substitutes for that analysis. Checked regressions compare zero, one and several
trivial result copies, and source fixtures cover nested descriptors, forwarding,
caller initialization, expansion, retained proofs and unsupported constructors.

Schema 52 also implements assignment materialization and full-expression
retirement in step 3. The importer retains Clang's full-expression materialization
and resolved trivial copy assignment; the lifetime event is independent of the
destructor inventory. Ordinary, expanded and retained descriptor regressions
preserve pointer identity and a saved reference into caller-owned backing through
assignment and retirement. Constant byte-interval containment connects the raw
result owner to typed constructor write ranges. Unknown pointer fields use the
ordinary typed read during aggregate copying, rather than acquiring the source
object's provenance; checked shared-engine coverage includes source retirement.

The unchanged pinned runtime `first(K)` now verifies for `0 <= K <= N`
under the accepted extent bound, preserving the receiver and result data pointer.
Ordinary, expanded and retained checks cover returned construction and forwarding.
A zero-count caller needs descriptor views alone: checked empty memory ranges
require no backing or loan transition. The local constructor contract also admits
zero. Aggregate materialization names are distinct from scalar call captures,
so a temporary in one function does not suppress another function's checked
nonaddressable scalar storage. Constructor helper calls and saved-reference
reads/writes across assignment retirement have source coverage.
`SpanPopBack` and its singleton-to-empty caller coverage remain pending. The selected design and bounds below
remain unchanged; no broader source profile or kernel certification redesign
is needed for the next step.

## Implementation handoff: remaining work

This is the selected implementation plan for the next agent. The shared engine
and Surface foundation are complete through commit `c4d6b951b`; PR
[#484](https://github.com/clicklang/click/pull/484) contains that checkpoint.
At handoff the worktree is `/workspace/click-aggregate`, branch
`codex/construction-storage`, with a public fork remote `lacker/click`.
Inspect the PR before publishing: continue the same PR while it is open and
not queued, following `AGENTS.md`. If it has merged, start from updated upstream.
Do not assume this recorded PR state remains current.

The checkpoint passed 5,433 enabled library/C++ import tests, all-target Clippy,
and the documentation build. A final focused/documentation run passed 33 tests
after combining the paired initialization checks. These are local results,
not a claim that CI or the unfinished target passed. The pinned local span
constructor already has ordinary, expanded and retained coverage.

### 1. Fix the source admission rule before adding return nodes

Keep the pinned LP64 C++20 / Clang 19.1.7 profile and locked library inputs.
Select **equivalence across permitted trivial result copies** for the first
returned-construction slice. Do not select one presumed ABI elision behavior.
Do not add general nondeterministic execution or change kernel certification
for this milestone. Broader address-sensitive source returns remain deferred;
the shared construction mode and direct local constructors still support them
where their existing source semantics justify construction at that address.

Use the C++20 rules in `[stmt.return]`, `[dcl.init]`, `[class.temporary]`,
`[class.copy.elision]` and `[expr.ass]` as the language references. In particular,
prvalue result-object construction does not by itself exclude the extra
parameter/result temporaries permitted for qualifying trivial classes.
Record the applicable C++20 wording and Clang-resolved operation in the source
admission documentation/tests when implementing the exporter change. An AST
`prvalue`, `isElidable` flag, or observed optimized IR is not a universal
no-copy proof. NRVO is not part of this slice.

Implement an internal, recomputed constructor eligibility analysis over the
validated typed function graph. A suggested home is
`src/languages/cpp/construction.rs`, called from schema validation. This is a
trusted frontend restriction on admitted source, not a new kernel rule or an
artifact Boolean that can grant permission. Memoize by declaration identity,
use the existing graph/depth budgets, and count deterministic work. Check:

- The result has a checked nominal layout, trivial destruction and the
  compiler-resolved trivial copy operations needed by this profile. Retain the
  existing exclusions for bases, unions, unsupported arrays and qualifiers.
- The constructor initializes every field in declaration order, using the
  existing scalar-store or embedded-constructor prefix. Embedded constructors
  must satisfy the same restriction recursively.
- Every stored value depends only on already evaluated by-value scalar/pointer
  parameters, supported constants, and checked pure arithmetic/conversions.
  A typed `Load` of a by-value parameter is allowed; a dereference, member read,
  global read, reference-parameter read, or projected place is not.
- No initializer value refers to the receiver or forms an address of its own
  storage, a parameter object, or a local. The receiver is allowed only as the
  destination of the validated member initialization, including child calls.
  Passing a pointer argument through unchanged remains allowed even when its
  value aliases the caller's eventual result object.
- Value helpers such as the pinned `std::to_address` and `std::__to_address`
  must themselves satisfy a transitive value-only restriction. Start with
  scalar/pointer by-value parameters and a return expression or return-call;
  reject memory access, address escape, local/static storage effects and
  recursion. Do not infer this property merely from a read-only contract.
  Their normal checked contracts are still required at modular calls.
- After the initializer prefix, admit no runtime effects or memory observations
  for this first slice. Already validated empty runtime branches are harmless;
  an `is_constant_evaluated` branch can be discarded only through the existing
  checked runtime-false interpretation. Successful `static_assert` declarations
  already have no runtime operation. Keep unsupported effects refused rather
  than skipping their source statements.

The reason this restriction suffices must be documented alongside it: after
arguments are evaluated, construction writes only the destination's modeled
fields and produces no pointer derived from that destination. The same
arguments therefore produce the same field values in distinct raw storage.
Each permitted trivial copy preserves those values exactly. Retiring the
intermediate object cannot invalidate a pointer created from its storage,
because none was created or exposed. Padding is not an admitted observable
value. This argument covers zero or multiple permitted copies and caller
argument aliasing; it does not invent separation. Memory reads inside the
constructor must remain excluded because aliasing could otherwise make direct
and intermediate construction observe different states.

Add a shared checked comparison fixture: construct a generic descriptor once
in the final destination, and once in a separate temporary followed by explicit
copy and retirement. Both must establish the same pointer/extent contract and
preserve existing backing authority. Use ordinary constructor and copy rules,
not a span intrinsic. Pair it with source-admission refusals for a self-address
constructor and a constructor/helper that reads through an aliasable pointer.
A refusal test checks unsupported source admission, not a false-proof probe.

### 2. Add bounded returned construction and forwarding

Extend `tools/cpp-exporter/main.cpp` and `src/languages/cpp/schema.rs` with
explicit resolved operations, for example `ReturnConstruct` and an aggregate
return-call form. Keep direct/list construction, forwarding and existing
`ReturnRecord` trivial lvalue copies distinguishable. Bump exporter schema 50
when its shape changes, update fixtures and regenerate affected locks through
the normal importer. Never edit a lock to bless a changed artifact.

For direct returned construction, require a matching complete-object constructor
and exact nominal result type, checked constructor arguments, nonthrowing
construction and trivial destruction. Reject NRVO candidates, move construction,
user-defined copies and unrepresented materialization/cleanup. Both
`return Descriptor(p, n)` and `return {p, n}` must retain the constructor Clang
actually resolved. For forwarding, require the exact admitted aggregate result
interface of the resolved callee and a compatible nominal type. Initially reject
mixed copy/construction return modes within one function rather than guessing
which mode a branch intended. Existing copy-only functions keep their old mode.

Carry the new variants through every existing traversal: source/span validity,
constant/reference inventory, reachable calls and signature checks, return-type
checks, terminal-flow checks, artifact budgets, lifetime validation and lowering.
Do not merely deserialize a node and rely on lowering to notice bad metadata.
Derive eligibility from bodies on import, including the transitive callee graph;
a forged target, function name, type, helper body or cleanup list must be refused.

In `src/languages/cpp/lowering.rs` and `interface.rs`:

- Select `with_construction_return(layout)` only for admitted functions.
  Preserve native result signatures and the Surface implicit storage resource.
  Aggregate construction calls are explicit result-producing operations, not
  scalar observer expressions: a receiver may be read-only while the hidden
  result must be writable. Preserve receiver/backing views through the ordinary
  resource transition rather than marking the whole factory as effect-free.
- Evaluate constructor arguments before destination writes, exactly once, using
  the scalar normalization machinery and fresh internal captures where needed.
  Preserve sequencing. For the initial multi-argument slice admit only argument
  evaluations whose order is fixed by the source form or whose lack of
  interference is checked; reject other order-sensitive combinations.
- Call the ordinary checked constructor with the hidden result address, then
  return that same address. Forwarding calls use the existing destination-aware
  call path; they allocate and copy nothing.
- Allow constructor arguments to be evaluated from the factory's receiver
  before construction, as in `first` calling `data()`. The value-only restriction
  applies to the constructor and its value helpers, not to those prior source
  reads. Those reads still need their ordinary contracts and authority.
- Restrict result-return exits to cleanup behavior already justified by this
  profile. Do not allow an unmodeled destructor or exit-time observation to
  distinguish intermediate from final construction.

Deliver this as a coherent increment with a generic pointer/uint64 descriptor,
nested extent construction, two forwarding factories, and a newly initialized
caller object. Check ordinary verification, expanded-proof reverification and retained
verification. No constructor inlining, external construction assumptions, source
rewrites, extra user parameters or user-managed return slots are needed.

### 3. Make initialization and assignment choose different storage

Extend the supported caller contexts explicitly; do not make every aggregate
expression an implicit copy or destination alias.

| Source context | Required lowering |
| --- | --- |
| `Descriptor x = make(...)` or equivalent admitted direct initialization | Allocate raw complete-object storage for `x`, then supply it to the admitted construction call. No final copy. |
| `return make(...)` in an admitted construction-return function | Forward the already bound hidden destination. Never retire it at callee exit. |
| `x = make(...)` with a resolved trivial assignment | Allocate a distinct raw RHS temporary; evaluate/construct there with old `x` still live; copy its fields into live `x`; retire only the RHS temporary at the full-expression boundary. |
| A live record lvalue copy | Preserve the existing explicit copy path and pointer values. |
| Other materialization, reference lifetime extension or aggregate argument contexts | Keep refused until their source lifetime and sequencing rules are represented. |

For assignment, initially require a simple validated LHS place and Clang's
resolved nonthrowing trivial assignment for the same nominal record. Do not
admit arbitrary effectful LHS evaluation or user-defined assignment. Retain
C++20 sequencing; in particular the RHS is evaluated before assignment changes
the LHS. Never reconstruct directly over `x` as an optimization.

Extend `src/languages/cpp/lifetime.rs`: its current destructor inventory alone
is insufficient, since trivial temporaries still have storage lifetimes.
Track generated materializations and the exact full-expression that owns them,
separately from destructor calls. Validate artifact lifetime annotations against
the derived expression structure. Lower retirement with
`c_end_automatic_lifetimes` after the consuming operation, in reverse completion
order where multiple supported temporaries occur. A return operand's
full-expression temporaries end after result initialization and before remaining
local cleanup; the supplied result itself belongs to the caller. If a newly
encountered control-flow path has no represented cleanup edge, refuse the source
shape until the edge is implemented. Do not silently lengthen a lifetime to
function exit.

Tests must distinguish old LHS reads from newly written fields, preserve the
LHS allocation identity, retire the generated temporary exactly once, and leave
caller result/backing storage alive. Keep the existing kernel self-pointer
copy/retirement regression: its pointer value survives copying but reads through
it fail after its source object expires. Do not turn that kernel fixture into
an unsupported universal C++ returned-`Node` claim.

### 4. Finish the unchanged pinned span path, including zero length

Use `pinned_span_fixture_with_dependencies` and the existing local-constructor
contracts in `tests/bitcoin_core_money_range.rs`. Keep the archive, source
hashes, compiler profile and native uint64 extent. Instantiate the unchanged
headers from a separately identified harness. Add only actual reachable locked
header dependencies; do not replace library functions with synthetic bodies.

The inspected pinned source is:

```cpp
// libstdc++ span:319
first(size_type __count) const noexcept {
    __glibcxx_assert(__count <= size());
    return { this->data(), __count };
}
// Bitcoin src/span.h:75
T& SpanPopBack(std::span<T>& span) {
    size_t size = span.size();
    T& back = span.back();
    span = span.first(size - 1);
    return back;
}
```

First prove runtime `first(K)` for `0 <= K <= N`, retaining the original backing
view and descriptor fields, with result data unchanged and native extent `K`.
A critical boundary is `K == 0`: the current local-constructor fixture requires
`1 <= count`, but `SpanPopBack` on a singleton constructs an empty descriptor.
Generalize the constructor's checked contract to allow zero; represent an empty
backing view with existing range/conditional-resource semantics as appropriate.
Do not strengthen the target to `N >= 2`, invent a positive-length view, or
require backing ownership for merely copying the descriptor pointer.

Then verify `SpanPopBack` under its existing intended contract in
[cpp-support.md](cpp-support.md#intended-contract):
`1 <= N <= 1,073,741,823`, mutable descriptor authority, an initialized readable
original backing range, and descriptor/backing separation. Prove native
unsigned subtraction and its bounded int32 range/index relation; never retag
`size_t` or silently truncate a bound. The updated descriptor has length `N-1`,
its pointer is unchanged, and the saved `back` reference still denotes the last
element of the original live allocation. The complete original backing frame
and its caller authority survive descriptor assignment and temporary retirement.

Include singleton and several-element cases, a symbolic bounded-length proof,
a caller that reads the returned reference, and a caller that writes through it
using its pre-existing owner. Also reject missing descriptor/backing authority,
out-of-range `first`, and an empty `SpanPopBack` input. No debug assertion is a
substitute for proving a precondition. Exercise ordinary, expanded and retained
verification for the imported result/assignment path and final target.

### 5. Validation, delivery and stopping points

Run focused tests after each coherent increment, then the affected library,
C++ import and pinned integration suites. Relevant commands are
`cargo nextest run --lib --test cpp_import`, selected
`--test bitcoin_core_money_range` cases, `cargo clippy --all-targets -- -D warnings`,
formatting/diff checks and the documentation gate. Build the pinned exporter
with `scripts/build-cpp-exporter.sh`; use the workspace's LLVM 19.1.7 setup and
`CLICK_CPP_EXPORTER` for exporter-dependent tests. Report skipped tests and any
missing Rust importer explicitly; full repository/merge checks remain CI's gate.
Keep ordinary C/Rust aggregate behavior unchanged and run their available
construction, copy/return, move/drop and scope-exit regressions.

Add deterministic multi-size checks for the eligibility graph, shared helpers,
nested constructors and temporary events. Analysis should visit each body once
per import, with indexed graph lookups; temporary retirement should depend on
the named objects, not scan unrelated state. Do not raise proof budgets or
change memory hashing as a substitute for fixing a regression. Existing empty
raw-storage hashes intentionally preserve legacy proof naming/performance.

Publish green increments in the order above to the thread's one open PR. Mark
the issue complete only when the actual pinned target and its callers pass,
its limitations are documented, and all three proof paths agree. Update this
issue and `cpp-support.md` to describe implemented behavior, not planned support.

No user decision is needed to implement this bounded profile. Routine unsupported
AST details, zero-length resources, diagnostics or proof-reverification defects are
implementation work: reproduce and fix them within the existing trust boundary.
Ask for a decision only if completing the target actually requires widening the
agreed scope, such as nontrivial cleanup/unwinding, a larger backing-range model,
or replacing the language-level equivalence restriction with a compiler/ABI-
specific identity guarantee. Present the concrete source case and alternatives
before asking. Do not reopen the resolved generic-proof certification discussion
or run false-proof probes; source-to-entry lowering remains trusted.

## Acceptance criteria

- Direct construction, explicit copying, forwarding and temporary retirement
  have distinct checked transitions with stable allocation identity and correct
  initialized-field state. No blanket elision or pointer rebasing rule is added.
- Missing initialization, authority or lifetime evidence, incompatible layouts,
  forged destination identities and unjustified separation are rejected. Include
  caller destinations aliasing arguments and partial-construction failures.
- Native C++ result signatures and field/reference contracts remain usable;
  generated certificates accurately represent the selected storage transitions.
- Ordinary verification, expansion/reverification and retained verification
  agree for the positive and negative kernel and imported-source regressions.
- Existing C aggregate return/copy proofs and Rust construction, aggregate
  return, move/drop and scope-exit proofs retain their behavior. Frontend
  interface updates are limited to what the shared design requires.
- Unchanged pinned span construction and `SpanPopBack` verify within their
  documented profile, including descriptor/backing separation, returned-reference
  validity and preservation of caller backing authority.
- Any changed verifier hot path has relevant deterministic scaling checks;
  no unrelated-fact scan, increased search budget or source rewrite substitutes
  for the required evidence.

General ownership, arbitrary nontrivial class values, broad destructor/unwind
support, Rust pinning, ABI coverage beyond the selected profile and a redesign
of all object lifetimes are separate scope. C-prefixed shared kernel names do
not require a repository-wide rename as part of this work.
