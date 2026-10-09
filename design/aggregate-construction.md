# Aggregate construction and return destinations

This is the implementation contract for
[shared aggregate construction](../issues/aggregate-construction-design.md).
The shared kernel supports a bounded complete-object construction return mode.
Existing C aggregate returns remain field copies; C++ returned construction
remains refused until source lowering and compiler evidence are connected.

The copy-return implementation now checks source initialization inside the
materialization transition, before allocating or copying a result. Kernel tests
also exercise an explicit destination through two nested procedure calls,
including its self-pointer and ownership transfer.

The shared memory model can also describe initially unwritten symbolic
storage without claiming that it is fresh or separate from arguments. Actual
writes establish initialization; resource naming does not. Initialization
survives value forgetting, intersects across branches, and follows checked
pointer equalities. Construction-return proofs use this initially unwritten
storage, with ownership supplied separately by their entry contract.

Caller allocation now has a separate `c_allocate_aggregate_destination`
operation. It allocates fresh automatic storage and its byte ownership without
seeding field values. Re-declaration uses the existing retirement and fresh
generation checks. Ordinary local declarations and the existing C++/Rust
constructor placeholder protocol retain their behavior.

`CAggregateReturnMode::Construction` now binds the hidden result to exact call
metadata before body execution. Completion validates the same pointer, layout,
live storage, and initialized value fields. Direct calls, forwarding calls, and
body-certified modular summaries share that destination; completing a result
does not allocate or copy. The initial kernel slice requires complete-object
storage, an explicit byte owner, and ordered non-overlapping scalar fields.
Union/array layouts, subobject destinations, exceptional construction, external
construction assumptions, and constructor callbacks remain refused. Contract
matching, state substitution, branch joins, and checked snapshot comparisons
include the destination and result mode. Source admission remains pending.

`c_end_automatic_lifetimes` makes a frontend-recorded expression boundary an
explicit shared statement. It uses the existing automatic-storage retirement
checks, removes only the named objects and their ownership, and preserves copied
pointer values and independently live backing storage. C++ lowering must still
select and emit those boundaries when returned construction is admitted.

## Surface and source boundary

Keep native result signatures, `result` field projections, and existing
`owns`/`views` clauses. A hidden destination is execution metadata, not another
source parameter or a user-managed resource. Users must not name compiler
temporaries, allocate return slots, or add tactics to retire those slots.

Before C++ admission, exercise `result.self == &result.value` through ordinary,
expanded and retained verification. Reuse existing address-expression syntax;
if aggregate result field addresses need lowering support, add that support
without introducing a new construction clause. Address formation checks live
storage and qualification, not field initialization or read authority.

## Operations and storage identity

The shared engine distinguishes allocation, construction, copying and retirement.
Frontend evidence selects the operation; the kernel checks its transition.

| Operation | Required evidence | Result |
| --- | --- | --- |
| Allocate storage | Checked size, alignment and allocation event | Fresh storage identity; no initialized field values |
| Construct into a destination | Exact destination, compatible layout, valid lifetime and write authority | Same identity, with the fields actually initialized by execution |
| Copy an aggregate | Initialized readable source fields and writable destination fields | Copied field values; pointer values are not rebased |
| Forward a construction destination | Compatible result interface and the same checked destination | No allocation, copy or additional ownership |
| Retire a temporary | Its recorded language lifetime boundary and required cleanup | Only that temporary's storage expires |

An address is allocation identity plus byte offset. Equal layouts do not make
objects identical. A subobject destination does not resize or replace its
containing allocation. Constructing into existing storage is not an allocation
event and cannot establish separation from arguments or other caller storage.

The first source slice uses fresh complete-object storage and forwarding of
that storage. The shared validation must still reject forged freshness and
unjustified separation when a supplied destination aliases an argument. Valid
overlap is judged by the actual reads, writes and resource transfer, not a
blanket rule that destinations cannot alias. Reuse of an already-live object's
storage requires explicit lifetime/replacement semantics and is not silently
admitted by this slice.

## Shared interface

Extend `CFunctionContractInterface` with an explicit aggregate result mode:
existing field-copy result or construction result. Keep the aggregate layout
and native result type. Include the mode in exact interface matching, callback
compatibility, hashes and retained proof identities. A certificate for one mode
cannot implement the other. C and Rust continue selecting their existing mode.
The mode specifies result storage, not a ban on copying inside a function:
a destination-return body may explicitly copy an existing value into its result
destination when its source semantics require that copy.

Represent the actual destination on the call execution, not on a reusable
function definition. It carries the exact pointer, selected layout, lifetime
owner and checked storage/authority evidence. Construction calls require this
binding; ordinary field-copy returns retain their existing fresh materializer.
Do not encode the destination as an ordinary user argument that could be
substituted independently of the result contract.

For body verification, introduce a symbolic destination constrained only by
the construction interface's checked preconditions. The callee constructs
there. At each call, instantiate that symbolic destination with the caller's
actual object, including alias relations with evaluated arguments. Bind
postcondition `result` to this same destination after successful completion.
Do not use the existing fresh `PointerBlock::Temporary` result for this mode.

Ordinary execution, modular summary application and retained checking must
consume the same destination relation. Expansion serializes enough evidence
to reconstruct it. A proof cannot change the destination, mint storage while
binding `result`, or restore a retired allocation. The caller supplies storage
authority once; nested forwarding transfers and returns the same authority.

Keep destination allocation separate from function effects. A fresh result
object's authority originates at caller allocation. A modular callee summary
must describe the constructor's actual writes, initialization and other
effects; it cannot obtain a general write frame from the presence of a result.

## Initialization and failure

Complete construction requires initialized values for all modeled value
fields, not necessarily padding bytes. An early field address can be stored
before the field's value is written. Observing the field value still requires
initialization and read authority. Copying a pointer never grants authority
over its pointee.

The existing `DeclareAggregate` constructor kind seeds scalar
placeholders so current constructor contracts can use the existing cell
machinery. Its frontend overwrite obligation is not a completion certificate
for the new result mode. The implementation must distinguish actual completed
initialization from these placeholders, using the existing initialization
machinery where possible. Do not publish a successful construction result
merely because symbolic cells exist.

On validation failure there is no accepted transition or completed result. On
a represented runtime failure, retain already-executed effects and the exact
initialized portion; do not roll them back or publish a fully live value.
Required cleanup belongs to the selected language's lifetime protocol. The
first C++ profile admits nonthrowing constructors with trivial destruction;
throwing/nontrivial construction stays refused until its cleanup transitions
are supported. Existing Rust move/drop behavior must remain unchanged.

## Returns, expressions and temporary boundaries

For construction returns, bind the destination before executing the body.
`return factory(...)` forwards that destination when the selected source
semantics justify it. Callee exit retires only callee-owned storage, not the
forwarded result. Completion checks initialization and binds the result;
there is no final field copy.

When source semantics require materialization, allocate a distinct temporary,
construct it, perform any explicit copy, and retire it at the recorded boundary.
Copying a self-pointer leaves it pointing into the source temporary. After that
temporary expires the copy may still contain the pointer value, but a read
through it must fail. A pointer into a separate caller backing allocation is
unaffected by retiring the descriptor that held it.

Initialization and assignment have different destinations. For example,
`span = span.first(n)` evaluates the returned descriptor with the old span
available, then performs checked trivial assignment. It must not construct
directly over the live left-hand descriptor as an unproved optimization.

## C++ admission evidence

The selected profile remains pinned LP64 C++20 with its existing Clang and
library inputs. Preserve the unchanged source and native extent types.

| Source case | Admission requirement |
| --- | --- |
| Direct local construction | Existing checked constructor destination |
| Copy from a live lvalue | Resolved trivial copy and checked layout; preserve pointer values |
| Prvalue factory result | Required result-object construction plus evidence accounting for any permitted trivial-class result temporaries |
| Forwarded factory result | Same requirements recursively, with exact destination forwarding |
| Named local return eligible for NRVO | Deferred until both permitted behaviors can be checked or the pinned compiled behavior is justified |
| Temporary followed by copying | Distinct storage, explicit copy and correct retirement |

Clang's expression category or an NRVO eligibility flag alone is insufficient
evidence of the selected execution. Before admitting each return shape, record
the language rule and compiler/ABI evidence that justify its transitions. If
multiple executions are admitted, prove the claim for each, or prove that their
observable behavior agrees for the selected claim. Keep the shape refused when
that evidence is missing. Do not infer address independence from trivial copying.

The identity-sensitive `Node` is the shared-kernel test oracle. It is not a
universal source claim about trivially copyable C++ returns. The first real
target is the pinned span descriptor: its pointer refers to independently live
backing storage, so permitted descriptor copies should preserve the target
contract. Establish that from checked constructors/copies, not a span intrinsic.

## Delivery and acceptance

1. Freeze the existing copy-return behavior and the contract in this document.
   Kernel regression coverage distinguishes copied self-pointers from result
   identity and descriptor storage from backing lifetime. This stage does not
   admit new source or implement destination returns.
2. Add the shared result mode and checked destination binding together with
   body execution, modular application and certificate support. Test direct
   construction, forwarding through two calls, complete initialization,
   layout/identity substitution, missing authority, aliasing arguments and
   partial construction. No standalone unchecked interface flag is a delivery.
3. Add materialization and retirement at expression boundaries. Test explicit
   copy, dead self-pointers, live external backing and caller-owned storage.
4. Admit the bounded C++ forms with compiler evidence, source regressions and
   hostile artifact checks. Confirm existing Surface syntax on self-address
   postconditions and all three proof paths.
5. Verify unchanged pinned span construction, runtime `first` and `SpanPopBack`,
   plus modular callers that read and write the returned reference with their
   existing backing authority. Retain native uint64 extent and the accepted
   `1 <= N <= 1,073,741,823` single-range bound.

Primary code owners are [shared interfaces](../src/kernel/primitives/contracts.rs),
[interface carriers](../src/kernel/primitives.rs),
[call execution and result binding](../src/kernel/functions.rs),
[statement execution](../src/kernel/eval/statements.rs),
[execution proofs](../src/kernel/proof/execution.rs),
[Surface contract lowering](../src/surface/lowering/annotations.rs), and
[C++ lowering](../src/languages/cpp/lowering.rs). The existing C++ identity
regressions live in [cpp_import.rs](../tests/cpp_import.rs).

Each implementation increment requires focused positive and negative tests,
agreement of ordinary/expanded/retained verification, and preservation of C
aggregate-copy/return and Rust construction/move/drop/scope-exit behavior.
Changed hot paths need deterministic multi-size work checks for destination
forwarding, field count and unrelated caller state. No whole-state scan or
larger tactic budget is an acceptable substitute. Use the repository's normal
local-check and CI gates and report exactly which checks ran.
