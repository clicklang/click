# C++ object model and shared memory semantics

## Status and purpose

This is the consolidated design target for the bounded C++ object model, with
the shared semantics required by C and Rust. It answers when the current
foundation is stable enough to resume C++ feature work. It does not claim full
C++ semantics or change the implementation by documenting a rule.

The implementation baseline includes the construction work recorded in
[Aggregate construction](aggregate-construction.md) and the explicit output
initialization work in [PR 646](https://github.com/clicklang/click/pull/646).
The [byte representation record](../docs/internals/byte-representation.md)
describes current byte behavior; the [C++ issue](../issues/cpp-support.md)
owns delivery status and source profiles. This document owns the combined
semantic target and stabilization criteria. Where current behavior falls short,
the gap is identified below. Historical delivery notes remain historical.

The principal conclusion is that typed cells, allocation identities, persistent
snapshots, indexed ranges, and the existing resource system remain useful.
We need one set of object and representation laws used by execution and proof,
including modular calls. Replacing memory with a flat byte array would not
resolve lifetime, provenance, or language validity and is not the proposed work.

## Decisions

1. Share the memory machinery and semantic operations across languages. Keep
   language-specific rules for object creation, valid access, moves, borrowing,
   and cleanup explicit at the checked frontend boundary.
2. Distinguish storage, objects, initialized bytes, valid values, and access
   authority. None of these is a substitute for the others.
3. Keep typed cells as the efficient representation. Typed and byte observations
   of the same supported object at the same snapshot must describe one value.
4. Make output initialization an explicit, body-checked effect, separate from
   value postconditions and ownership. Mentioning a read in a proposition must
   not create initialized storage.
5. Preserve destination-directed construction, ordinary value copying, and
   explicit lifetime events as distinct operations. A callee's destination is
   not fresh unless the caller's allocation and contract establish that fact.
6. Stabilize the already selected profile before adding owning containers or
   broader object-lifetime features. The acceptance matrix below defines that
   milestone; verifying one more helper alone does not.

These consolidate the accepted direction. The common typed/byte observation
rule and the admission audit below are remaining implementation work, not
newly delivered capabilities. No new Surface syntax is proposed here.

## The bounded target

Use the existing pinned x86-64 Linux LP64 C++20 profile, eight-bit bytes and
little-endian integers. Retain the compiler, header, declaration-identity and
layout checks of each admitted source fixture. Native integer contracts with
checked C++ identities remain the contract boundary, including authenticated
`std::byte`. An unrelated enum with the same representation gets no byte-access
privilege.

The stabilization target covers the existing scalar locals and references,
plain records and supported subobjects, bounded construction/return and trivial
assignment, full-expression temporaries, existing RAII/cleanup cases, and the
selected span/byte-output decoder prerequisites. The first new representation
bridge is a declared automatic uint32 object observed through its four bytes.
It is not a proposal to admit every integer width, heap object, array element,
or record field as a reconstruction destination at once.

Already delivered nontrivial local destruction and bounded exceptional cleanup
remain supported. The narrower restrictions on construction returns do not
retroactively restrict every C++ object to trivial destruction.

Placement construction and storage reuse, unions, general inheritance and
virtual dispatch, broader exceptional construction, arbitrary owning containers,
concurrency, and other targets are outside this stabilization milestone.
Adding them must explicitly extend this design. Their absence does not prevent
a sound, useful bounded model.

## Semantic state

The following are distinct facts the model must represent or derive from checked
evidence. They need not become six new maps or one large mutable object record.
Static importer evidence is sufficient for facts that cannot change within the
admitted profile; dynamic facts belong in snapshots or checked execution state.

| Component | Meaning | Does not establish |
| --- | --- | --- |
| Storage | Allocation identity/generation, extent, alignment, and live storage | An object of an arbitrary requested type |
| Object | Declared/admitted type, layout, containing object and subobject, lifecycle phase | Initialized contents or permission |
| Representation | Typed values and byte fragments describing that storage at a snapshot | Legal access by every source-language type |
| Definite initialization | The selected bytes have been written or otherwise validly initialized | A particular value, or validity for every type |
| Value availability and validity | A language-level value may be used in this phase with this type | Ownership of all reachable storage |
| Authority | Permission to read/write or a checked loan/resource over a range | Freshness, initialization, or object lifetime |

Unknown contents are different from uninitialized contents. Havoc can forget a
value while preserving definite initialization and the declared object type.
Conversely, obtaining ownership of raw storage does not give it a value.

### Addresses and objects

The existing block-and-offset pointer is the address carrier. A field stays at
an offset in its containing allocation; it does not become a fresh allocation.
Copying a pointer copies its provenance and offset without rebasing it. A copied
self-pointer therefore continues to point into the original object.

An address plus allocation bounds is not a complete typed-access justification.
Access also needs an admitted object/type, alignment, the relevant object or
array domain, lifecycle validity, initialization where required, and authority.
For example, owning a whole record does not by itself authorize scalar pointer
arithmetic across its unrelated fields. A cast changes the access description;
it does not create an object, enlarge a pointer's array domain, or grant access.

For the first profile, retain block/offset and existing layout evidence. Audit
that each admitted operation has the necessary object and access-domain evidence;
add a shared descriptor or certificate field where evidence is missing. Do not
introduce independent object identities throughout memory merely for uniformity.
General replacement in the same storage will require an explicit object-generation
and pointer-designation decision when that feature is selected.

### Pointer designation: a confirmed shared gap

The admission audit reproduced [a soundness defect](../bugs/pointer-arithmetic-crosses-scalar-subobject.md)
in both C and C++: a pointer one past the first scalar member of a record can
read the second member. The shared evaluator checks allocation/range bounds and
finds the second member's cell at the same address. That is insufficient under
either language's pointer rules. This turns the earlier access-domain audit
obligation into mandatory implementation work for the existing profile.

Preserve two semantic identities: the storage address used for aliasing and
cell lookup, and the object/array designation used to justify access. A pointer
value must carry or reference checked designation evidence that survives
copying, storage/reload, casts, calls and snapshot transport. This cannot be
recovered just from the numeric address, current read width, or whichever
ownership range happens to contain the address.

The bounded designation consists of the relevant object/array identity, element
type and extent, position within that domain (including one-past), and the
lifetime evidence needed for access. It may use shared immutable descriptors
rather than expanding every pointer with a complete layout. Scalar members
have a one-element domain; actual arrays retain their array domain. Taking a
member address selects that member's domain without allocating new storage.
Pointer arithmetic preserves the selected domain and checks its bounds.
Dereference separately requires a position designating a live object, not its
one-past endpoint.

Address equality continues to support memory alias reasoning. It does not
transport dereference validity between differently designated pointer values.
The representation must preserve this distinction in equality/hashing and proof
substitution; adding a field to `CPointerValue` while discarding it through
`into_pointer()` or treating it like an ignored qualifier would not suffice.
Pure memory observation at an address and executable typed dereference need
different validity interfaces even when they share the same value observer.

Input array extents must come from a checked declaration or explicit contract
validity obligation that the caller discharges for the actual pointer domain.
An ownership clause alone must not silently enlarge an already known member
domain. The implementation audit must identify those obligations at modular
boundaries before claiming general pointer-parameter coverage.

For example, a helper reading `p[1]` may require a two-element input domain.
Its caller cannot satisfy that requirement by combining ownership of two
adjacent scalar fields and passing the first field's address. Actual two-element
array storage can satisfy it. This distinction must survive resource splitting
and rejoining, so the object-domain evidence belongs beside authority rather
than being reconstructed from the resulting contiguous owned range.

For byte representation, an admitted representation-view operation selects the
bytes of one designated object under the selected language profile. It does
not turn every byte of the enclosing allocation into one permissible array.
This must use the same domain mechanism as ordinary typed pointers.

### Lifetime is not a single initialized flag

Storage can exist before construction and after an object's lifetime. A scalar
declaration without an initializer can establish an object whose bytes are still
unwritten. A constructor can initialize and access some subobjects before the
whole result is complete. A successful constructor summary certifies completion
of its modeled value fields; it does not initialize padding.

Destruction has a language-defined phase with permitted accesses and cleanup
obligations. Do not model it as simply invalidating every access before running
the destructor body. Normal exit, early return, full-expression cleanup and the
admitted exceptional paths must use the same checked lifecycle protocol.
Unsupported exceptional construction remains refused; failure must not invent
successful completion or roll back effects that already occurred.

Rust adds an important independent distinction: a move can consume the usable
value while the storage and old bits remain. Rust live/drop state must prevent
use of that value. A C++ move constructor generally leaves its source object
alive and destructible. Sharing an operation named "move" cannot erase that
difference. Similarly, C++ references do not acquire Rust's exclusive-borrow
rules simply because both use the shared pointer carrier.

## Shared operation contract

Each frontend must justify these operations with its own checked source rules.
The kernel then applies their shared effects consistently, including at calls.

| Operation | Required evidence | Resulting effect |
| --- | --- | --- |
| Allocate storage | Checked extent/alignment and allocation kind | Fresh live storage and the specified owner; no fabricated contents |
| Select construction destination | Exact pointer, layout, range and authority | Bind that destination before execution; no extra freshness assumption |
| Begin object/subobject use | Admitted declaration or construction rule | Record/validate type and lifecycle phase; no arbitrary reinterpretation |
| Initialize scalar/field | Valid destination, conversion, phase and write permission | Store the converted value and mark the written range initialized |
| Read typed value | Valid object/access type, phase, alignment, initialized representation and read permission | Observe the value at that snapshot |
| Assign/store | Existing writable object and valid converted value | Update affected representation; preserve object identity |
| Copy a value | Valid initialized source and destination operation | Copy modeled values, including pointer provenance; no pointer rebasing |
| Copy representation | A checked representation-copy rule and covered source/destination | Transport supported representation and initialization under that rule |
| Complete construction | The selected destination and required initialized value fields | Certify completion; no allocation, copy or padding initialization |
| Move or consume | Language-specific move and cleanup evidence | Transfer value/authority as specified; change source availability only as justified |
| Destroy/end lifetime | Checked cleanup order and lifecycle event | Apply cleanup, retire the relevant object/storage and resources as appropriate |

Initialization is not assignment with a temporary const override. Shared scalar
initialization performs evaluation and conversion, initializes once, then freezes
the admitted const destination. Assignment must not reuse that privilege.

Value copying and representation copying have different preconditions. Existing
aggregate field-copy returns do not imply byte-for-byte padding preservation.
The recognized `memcpy` contract is a separately reported external assumption
with a checked kernel representation-copy effect. Neither mechanism licenses
arbitrary object creation from four byte cells or pointer creation from bits.

Construction-return mode continues to bind the caller-selected destination
before the body. Ordinary copy returns continue to copy. Trivial assignment
from a constructed RHS uses a distinct temporary followed by assignment and
full-expression retirement. Ending that descriptor temporary does not end the
lifetime of independently owned span backing storage.

## One representation, consistent observations

### The law to implement next

Execution loads and specification observations must agree whenever both refer
to the same admitted object, byte range and memory snapshot. A modular call
changes which facts are known; it must not change what a byte or typed read
means. The current execution-only byte view violates this intended uniformity:
its useful relation is unavailable to specification byte postconditions.

For the initial declared uint32 profile, let `w` be its value at snapshot `M`
and `b0` through `b3` be its initialized representation bytes at that same
snapshot, in increasing address order. The semantic equations are:

```text
bk = (w >> (8 * k)) & 255             for k = 0, 1, 2, 3
w  = zext(b0) | (zext(b1) << 8) | (zext(b2) << 16) | (zext(b3) << 24)
```

These are semantic notation, not proposed proof syntax. Their applicability
requires the selected target, a known declared uint32 object, valid byte access,
the corresponding ranges/snapshot, and sufficient initialization for the
observation being used. Four bytes allocated as a byte array do not establish
a uint32 object. A requested load width, cast, or allocation size cannot supply
the missing type evidence.

A typed store followed by byte observations uses the first equation. Four
initialized byte writes, in any order, followed by a typed load use the second.
A partial byte update to an existing initialized word preserves the remaining
bytes. After modular output initialization, postconditions fixing all four bytes
must determine the same word as inline execution would. Old-snapshot bytes
cannot reconstruct the current word after a write.

The initial implementation should expose one guarded representation observation
operation and checked projection/reconstruction rules to both execution and
logical loads. It may retain separate APIs for program reads and pure term
construction: program reads have authority and definedness obligations that
building a symbolic proposition does not discharge. In particular, constructing
a logical read term or naming an unknown value does not initialize memory,
start a lifetime, or make an otherwise invalid program read legal.

### Representation and implementation

Keep typed cells authoritative for supported complete values, with byte fragments
and lazy projections where needed. This is an encoding of the common semantics,
not a second independent memory. A store must update or invalidate overlapping
views; a proof cache must include the memory snapshot and interpretation needed
to prevent stale reuse. Joins keep only facts and definite initialization justified
on both paths. Havoc removes value constraints without reviving earlier contents.

Pointer representation remains opaque in this profile. Complete representation
copy can preserve pointer provenance under its existing checked rule; byte
editing cannot manufacture it. Float, Boolean, padding and other unsupported
representations remain outside the new projection/reconstruction rule. A model
can preserve padding without exposing a determinate padding value to a proof.

No eager expansion of every object into bytes is required. Lookup starts from
the selected object/range, uses indexed overlap and declaration evidence, and
does bounded work per supported scalar width. Symbolic ranges use the existing
indexed interval machinery. Unrelated heap cells, resources and propositions
must not be scanned. Proof checking must remain proportional to the selected
input and relevant delta, up to indexing factors. A representation certificate
records the selected evidence rather than asking retained checking to rediscover
an unbounded set of equalities.

An explicit reconstruction lemma can expose the shared law to users when useful.
It must be derived from that law, not become an alternative per-helper memory
model or a mandatory workaround for ordinary typed/byte consistency.

### Implementation boundary for the uint32 bridge

The shared observation interface must take the selected snapshot, address,
observation kind and checked declared-object evidence. The observation kind
includes width: a uint8 read and a uint32 read at the same address are not
interchangeable terms. Execution additionally checks access designation,
authority and definedness; logical term construction cannot discharge them.

For a supported declared uint32 object, choose one canonical symbolic word for
each relevant snapshot/object observation. Its four byte observations are
projections of that word. A checked packing rule relates four known byte
observations at that snapshot to the word, including after a modular call.
Neither projection nor packing allocates storage or sets initialization bits.
The explicit initialized-range effect supplies that independent evidence.

Implement this through the shared load/representation layer, with the existing
`canonical_form_of_load` and `LoadKind` boundary audited for width and snapshot
identity. Keep an explicit checked rule when normalization alone cannot connect
the observations. The rule's certificate must name the object declaration,
target representation, relevant initialization evidence and exact observations;
retained checking must not repeat a search over arbitrary ambient equalities.
Reject forged widths, adjacent-object byte mixtures, stale snapshots, three-byte
coverage and unsupported target/type evidence.

This is the implementation contract, not a requirement to replace every existing
load term immediately. Existing complete typed cells and direct byte-store
normalization can remain efficient encodings if both reduce to the same law.
First prove the relation in the shared C fixture, whose character-pointer rules
already supply the source-language representation traversal. Claim C++ coverage
only after its separate byte-access profile is settled.

## Contracts, proof entry and modular calls

Keep four kinds of information separate: value propositions, initialized-range
effects, authority, and object/lifecycle evidence. For example, the delivered
`ensures initialized(p[0..N]);` atom supplies definite initialization, an ownership
clause supplies access, and byte equalities supply values. None silently supplies
the others. It also does not create a different object type in the range.

The current atom is deliberately bounded: a top-level normal postcondition on
a mutable native byte-pointer parameter, zero start and constant byte count,
with the address frozen at entry. Parameter reassignment cannot redirect the
guarantee. Body verification starts that output footprint unwritten; holes,
no-op bodies and premature reads are rejected. Calls transfer precisely the
checked initialization effect. Conditional, exceptional, callback and ordinary
external initialization guarantees remain outside this profile.

Explicit external construction-return contracts are a distinct existing
assumption mechanism. They may assume completed initialized value fields for
the designated result, and are reported as external assumptions. That exception
must not accidentally authorize external initialized-range effects on arbitrary
output buffers.

Proof-entry naming must be observational. It can give a name to a value allowed
by the contract, but cannot execute a store into raw output or turn a constructor
placeholder into a completion certificate. Body checking must consider every
aliasing arrangement admitted by the entry contract. Constructing a convenient
fresh proof slot is not a substitute for proving separation.

Copy materialization, initialization queries and snapshot transport must receive
the actual checked call context. Discarding its separation facts can make valid
input cells appear to overlap unwritten output; assuming separation without the
facts would be unsound. Both problems belong at the shared operation boundary.

That context includes separation justified by the ownership partition, as well
as explicit separation propositions. A raw destination must not make every
possibly aliasing symbolic input unreadable after the contract has established
the relevant separation. Conversely, different pointer names are never enough.
Constructor value-field footprints and padding must be distinguished: requiring
authority over value fields must not silently become a requirement to own or
initialize all padding. Resolve these questions by checked range and object
evidence, not by freshening the destination or seeding it with input values.

Execution, modular summaries, expansion and retained checking must apply the
same laws. A checked summary carries the operation's destination/effect metadata
and binds it to actual arguments; it cannot replace the caller's object type or
provenance with a convenient callee interpretation. Semantic changes require
the existing proof/artifact identity invalidation discipline.

## What stays language-specific

| Question | C | C++ | Rust |
| --- | --- | --- | --- |
| Why does an object/value of this type exist? | Admitted declaration or supported allocation/effective-type rule | Checked declaration, layout and construction/lifetime rule | Compiler-derived storage, initialization and move/drop protocol |
| Why is this alias/access legal? | Selected C type and character-access rules | Selected C++ type, object/subobject and authenticated byte-access rules | Admitted reference/borrow/raw-access rules and compiler evidence |
| What does copying or moving mean? | Admitted scalar/aggregate copy | Resolved copy/move/assignment operation and allowed elision/temporary behavior | Copy versus consuming move and associated availability/drop state |
| When does access cease? | Selected C lifetime and pointer-validity policy | Object/storage lifetime plus construction/destruction access rules | Storage lifetime, value availability and loan validity |

This table is an obligation on admitted operations, not a claim that every
language rule listed has a general implementation. In particular, the existing
C11 dead-pointer policy must not silently become the rule for every C++ pointer
comparison or Rust value. C's character-alias rules must not grant C++ access
through every same-sized scalar type. Unsafe Rust is not implicitly covered by
safe-Rust import evidence.

The C++ importer must retain enough evidence to distinguish source operations:
resolved constructor/copy/assignment identity, destination category, object and
field layout, qualifiers, reference versus value result, and cleanup sequence.
Clang accepting a translation unit is necessary extraction evidence, not proof
that arbitrary runtime accesses in it have defined behavior.

Preserve the construction design's copy-equivalence restriction. C++20 can permit
additional temporaries for some trivial class results; selecting a result object
in the kernel does not prove that all source executions preserve its physical
address. An identity-sensitive self-pointer example tests the kernel destination
mechanism, but is not by itself a sound source-level trivial-return theorem.
Optional NRVO and broader identity-sensitive returns stay outside that admission.

The audit must also identify the exact C++20 rule or adopted defect resolution
justifying byte traversal over the selected object's representation. Do not
silently use a later standard's wording or an LLVM byte-address calculation as
the source-language justification. If the pinned profile needs an explicit
extension or cannot justify an admitted pattern, report that boundary before
expanding it. This is a source-semantics audit obligation, not a claim that the
existing fixture has a reproduced defect.

### Byte access requires an explicit source-profile choice

The audit compared the imported `c++20` profile with
[N4861 expressions](https://github.com/cplusplus/draft/blob/n4861/source/expressions.tex)
and [N4861 basic types](https://github.com/cplusplus/draft/blob/n4861/source/basic.tex).
The aliasing exemption in [basic.lval] allows `char`, `unsigned char` and
`std::byte` access, but does not by itself supply an array of representation
bytes to the pointer-arithmetic rules in [expr.add]. The trivially-copyable
byte-copy guarantees in [basic.types] are a separate rule and do not justify
every in-place cast-and-index sequence.

The authors' [P1839R5 rationale](https://github.com/timuraudio/p1839/blob/main/P1839R5.md)
explicitly identifies the object-representation pointer problem and limits that
revision to reading; it excludes writing because of additional difficulties.
The [committee tracking issue](https://github.com/cplusplus/papers/issues/592)
records later revisions, including R7. That history is not evidence that the
current pinned C++20 profile already includes a suitable read/write rule. Do
not silently import a proposal or call it an adopted defect resolution without
checking its exact wording and status.

The source-profile choice is therefore explicit: either retain literal C++20
coverage and pause the unchanged cast-and-index byte writer, or specify an
additional bounded implementation contract for the pinned compiler. The latter
would cover declared uint32 representation bytes, endian mapping, write/read
validity and object-domain preservation, with its assumptions reported in the
verification profile and included in artifact identity. Compiler execution
probes can corroborate that contract, but are not a proof of a general C++
standard guarantee. A `memcpy`-based source target is another standards-based
route when that is the original program; it is not permission to rewrite the
selected unchanged decoder.

This choice blocks expansion of the byte-writer profile, not independent
constructor/observer regression repairs. It does not change the existing
decision to use native uint8 contracts with authenticated enum identities.

## Implementation assessment

| Area | Current evidence | Remaining obligation |
| --- | --- | --- |
| Allocation, ownership and snapshots | Shared block/offset storage, persistent memory, exact local byte ownership | Reuse; audit object/access-domain evidence at admitted operations |
| Construction and copy | Destination allocation/binding/completion, field-copy returns, constructor summaries and temporary retirement | Check that every path obeys the combined lifecycle laws; preserve language restrictions |
| Initialization | Raw output state, indexed initialized runs, joins, explicit normal output effects | Apply consistently at all entry/copy/summary boundaries; no naming stores |
| Integer byte view | Execution projection/update and declared automatic uint32 assembly | Common guarded observation semantics for execution and specifications |
| Pointer representation | Provenance-preserving complete-cell copy; byte forging refused | Preserve refusals and provenance under common observation machinery |
| Language validity | C++ identity/layout/lifetime checks; Rust move/drop and borrowing checks | Make the evidence boundary explicit; do not infer legality from ownership alone |
| Modular byte-output value | Initialization and individual byte results check | Prove the exact typed word from those same byte facts |

Implementation starting points are `CBlock`/`CMemory` in
[`src/kernel/primitives.rs`](../src/kernel/primitives.rs), initialization and
proof-entry naming in
[`memory_state.rs`](../src/kernel/primitives/memory_state.rs), byte observation
in [`byte_view.rs`](../src/kernel/eval/byte_view.rs), and destination completion
in [`construction_return.rs`](../src/kernel/functions/construction_return.rs).
The C++ scalar and lifetime modules and Rust move lowering retain the language
evidence; moving all their policies into an undifferentiated kernel flag would
be a regression.

The recent failures expose boundary inconsistencies rather than evidence that
typed cells must be replaced: proof-entry naming could initialize raw output;
copy checking lost useful separation context; execution byte reads and logical
byte reads had different available relations. The output-initialization work
changes the first two boundaries, but its CI also exposed constructor-input and
returned-observer regressions. The returned observer is repaired by retrying
logical input naming with checked explicit separation facts; its unchanged
ordinary, expanded and retained proofs and negative mutation checks pass. The
[constructor-input bug](../bugs/raw-construction-destination-hides-initialized-input.md)
remains: existing RAII proofs lose initialized input reads at the padding
boundary. Neither repair may weaken existing contracts. The third inconsistency
is the concrete missing semantic bridge. The object/access-domain audit also
confirmed the pointer-designation defect above; it must be repaired before
claiming the bounded model stable.

### Audit ledger

The following records the focused audit, not a certification of all C++ behavior.
Source admission, execution and proof checking each have separate obligations.

| Path reviewed | Evidence inspected | Result / required action |
| --- | --- | --- |
| Standard byte identity | `cpp/scalar.rs`, `cpp/validity.rs`, exporter cast checks and pinned-declaration tests | Nominal identity and scalar backing are checked; this does not establish traversal semantics |
| Member address and arithmetic | `cpp/lowering.rs`, `CPointerValue`, `eval/operators.rs` and `eval/memory_loads.rs`; original C/C++ probes | Confirmed missing designation check; fix before claiming this bounded pointer model stable |
| Construction return | `cpp/construction.rs` and the implemented construction design | Preserve value-only/copy-equivalent admission; kernel destination identity alone is insufficient for source return identity |
| Entry initialization | Raw markers, naming, checked entry facts and the constructor regression | Keep raw output unwritten; do not infer complete storage separation from field owners with padding gaps |
| Returned observer | Recorded proof trace and unchanged integration test | Input naming now uses already checked explicit full-range separation; ordinary, expanded, retained and negative checks pass, while padding remains unresolved |
| Byte/word values | `eval/byte_view.rs`, declared scalar metadata and exact modular word refusal | Direct execution has a bounded encoding law; logical/modular observations still need the shared bridge above |
| Rust availability | `rust/lowering/moves.rs` storage events and checked live/drop flags | Preserve value consumption independently of bytes and storage; a C++ move must not reuse Rust's consuming semantics |
| Scalar initialization | Shared initialized declaration, conversion and const-freezing protocol | Retain the distinct initialization transition; ownership and a named logical cell cannot replace it |

The constructor-padding question remains open at the implementation boundary.
Splitting a raw marker into only value fields would make padding fall through
the external-memory read path unless another checked guard protects it. Keeping
the full marker while asserting separation from only the field owners is also
invalid. A sound repair needs explicit object/extent/lifecycle evidence or a
representation that separately protects padding and justifies the other input
objects. The new designation work must establish that evidence; the audit does
not authorize either shortcut.

## Stabilization work and exit criteria

Pause expansion of the C++ feature profile for the following work. Keep changes
reviewable and preserve all existing source fixtures. These are completion
conditions, not a promise of a fixed number of PRs.

1. **Record the admitted operations and their evidence.** Audit the selected
   scalar, field, span, construction, assignment and byte-access paths against
   the state and operation tables above. For each, identify where type, access
   domain, lifecycle, initialization and authority are checked. Resolve missing
   evidence in the shared operation or narrow admission with a regression;
   surface any actual source-profile choice before proceeding past it.
   The confirmed member-pointer defect requires checked designation across
   arithmetic, loads, copies and calls; it cannot be closed by a documentation
   note or a syntax-only rejection of the initial probe.
2. **Unify the selected representation observations.** Implement the declared
   uint32 law once, with checked rules usable by execution, logical observations
   and modular calls. Preserve byte/pointer/type refusals and efficient lookup.
   Turn the exact value claim in
   [`modular_byte_output_word_value_requires_representation.md`](../mdtests/modular_byte_output_word_value_requires_representation.md)
   into a positive regression without weakening it or rewriting its source.
3. **Close lifecycle and call-path inconsistencies.** Check proof-entry naming,
   scalar initialization, constructor completion, copy materialization, havoc,
   branch joins and cleanup against the common laws. Reuse passing tests where
   they already demonstrate the obligation; change implementation only for
   demonstrated gaps. Legacy frontend placeholders must remain unavailable as
   general initialized-object evidence.
4. **Demonstrate consistency and bounded cost.** Complete the acceptance matrix
   below using the existing proof modes, hostile-artifact tests and deterministic
   work measurements. Include unrelated-memory growth to catch global scans.
5. **Resume the selected unchanged decoder proof.** Keep its exact byte-to-word
   result and span bounds, initialization and backing-lifetime claims. Record
   source/profile/dependency coverage and update the C++ issue. Any remaining
   algorithmic proof work should use this model rather than invent new object
   semantics for that helper.

| Obligation | Positive witness | Required negative/boundary witness |
| --- | --- | --- |
| Representation coherence | Typed store to bytes; four byte stores to declared word; partial byte update | Wrong type, incomplete bytes, stale snapshot, unsupported representation |
| Modular coherence | Inline and body-certified modular byte writer establish the same exact word | No-op/hole writer; value proposition or ownership without initialization |
| Destination and copy | Nested destination forwarding; lvalue copy; separate RHS assignment | Rebound destination, missing field, copied self-pointer wrongly rebased |
| Aliasing and frames | Contract-permitted aliases; checked separation; sibling/backing preservation | Freshness inferred from construction; lost or fabricated separation evidence |
| Lifetime and availability | Existing RAII, full-expression retirement and Rust move/drop witnesses | Dead temporary access; use after Rust move; destruction consuming independent backing |
| Access justification | Admitted scalar/subobject/array and authenticated `std::byte` access | Same-sized fake enum, cast-created object, unjustified cross-subobject arithmetic |
| Proof modes and trust | Ordinary, expanded and retained proofs of the selected source fixtures | Mutated destination/layout/type/effect metadata; older semantic identity |
| Scaling | Selected object/range work with growing unrelated memory | Heap-wide byte expansion or proposition scanning for a local operation |

The milestone is complete when every selected operation has an identified
semantic justification, these witnesses pass, and the unchanged decoder uses
the shared model with its original claim. C and Rust must retain their existing
construction, initialization, resource and lifecycle regressions; use paired
cross-language witnesses where the underlying operation is shared. Do not create
duplicate tests merely to populate the table.

This is a finite stabilization target: the representation bridge, checked
pointer designation for the admitted profile, an audit of the remaining
boundaries, and correction of demonstrated inconsistencies. The audit established
that pointer designation is a second concrete shared semantic gap; the earlier
estimate of just one known bridge was incomplete.
It is not a promise that all of C++ can subsequently be added without kernel
changes. Ordinary helpers within this profile should require contracts, proofs
or importer coverage. A feature that introduces a genuinely new object behavior,
such as replacement in live storage or overlapping union members, must explicitly
reopen the relevant design boundary before implementation.

## Alternatives not selected

- **A canonical byte blob for all memory.** It does not explain pointer
  provenance, object existence or legal access, and eager byte expansion harms
  scaling. Typed cells with coherent observations meet this milestone.
- **A C++-specific second memory model.** It would duplicate call, resource,
  snapshot and proof-checking semantics while leaving C and Rust inconsistencies.
  Language-specific admission over shared operations is the intended boundary.
- **Initialization inferred from mentioned reads.** This lets a proposition
  create the state needed to make itself meaningful. Explicit checked effects
  preserve the distinction between initialized unknown output and asserted values.
- **Per-decoder reconstruction intrinsics.** They conceal the missing relation
  between ordinary typed and byte observations. Derived lemmas remain useful;
  helper-specific semantics do not establish a stable object model.
- **A universal lifetime/alias policy for all three languages.** It confuses
  C++ construction and moves, C object access, and Rust availability/borrowing.
  Shared machinery must preserve those differences.
