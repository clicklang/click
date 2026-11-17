# C++ object model and shared memory semantics

This record states the accepted object-model laws shared by supported C, C++
and Rust operations. Current implementation evidence and completed bounded
entry/call checks belong to the
[native-interface audit](object-model-current-audit.md#native-interface-evidence-matrix).
This record does not require recovery of PR #646 or its retired implementation.

## Decisions and scope

1. Share semantic operations and memory machinery; keep language-specific
   creation, access, moves, borrowing and cleanup at the frontend boundary.
2. Distinguish storage, object/type validity, initialized bytes, values and
   access authority. None substitutes for another.
3. Keep efficient typed cells with coherent typed/byte observations at one
   state, rather than introducing an independent byte memory.
4. Establish output initialization from checked body effects, independently of
   value postconditions and ownership.
5. Keep allocation, destination-directed construction, copying, assignment
   and lifetime end distinct. A construction destination is not inherently
   fresh or separate from arguments.
6. Each admitted source slice needs evidence for its own object/lifetime
   rules. The completed audit records the bounded acceptance boundary; there
   is no blanket C++ feature freeze or obligation to implement archived APIs.

The selected profile includes supported scalar locals/references, plain
records/subobjects, bounded construction and returns, trivial assignment,
full-expression temporaries, and admitted cleanup paths. Construction-return
restrictions do not remove already supported nontrivial local destruction.
Placement/replacement, overlapping unions, general inheritance/virtual dispatch,
broader exceptional construction and other targets require separate rules.
The [C++ coverage item](../roadmap/cpp-support.md) owns feature expansion.

## Semantic state

The following are distinct facts the model must represent or derive from checked
evidence. They need not become six new maps or one large mutable object record.
Static importer evidence is sufficient for facts that cannot change within the
admitted profile; dynamic facts belong in states or checked execution state.

| Component | Meaning | Does not establish |
| --- | --- | --- |
| Storage | Allocation identity/generation, extent, alignment, and live storage | An object of an arbitrary requested type |
| Object | Declared/admitted type, layout, containing object and subobject, lifecycle phase | Initialized contents or permission |
| Representation | Typed values and byte fragments describing that storage at a state | Legal access by every source-language type |
| Definite initialization | The selected bytes have been written or otherwise validly initialized | A particular value, or validity for every type |
| Value availability and validity | A language-level value may be used in this phase with this type | Ownership of all reachable storage |
| Authority | Permission to read/write or a checked loan/resource over a range | Freshness, initialization, or object lifetime |

Unknown contents are different from uninitialized contents. Havoc can forget a
value while preserving definite initialization and the declared object type.
This applies to symbolic contract inputs as well as local objects: forgetting
an admitted complete typed cell retains its initialized bytes. Adjacent cells
in a symbolic run remain one interval, without enumerating its elements.
Conversely, obtaining ownership of raw storage does not give it a value.

## Addresses, provenance and lifetime

Pointers retain allocation identity and byte offset for address lookup, plus
the provenance required for legal access. Equal numeric addresses do not
supply another pointer's provenance, authority or lifetime. Copying a pointer
preserves its value; copying an object containing a self-pointer does not
rebase that pointer into the copy.

Formation, including one-past formation, is separate from dereference. A
containing allocation does not justify traversal across unrelated scalar
subobjects. An unseen pointer needs bounds evidence, and native reference
binding alone cannot initialize an unwritten C++ referent. The delivered
bounded rules and accepted C cast policy are in
[Pointer subobject extents](pointer-subobject-extents.md) and
[Pointer/integer representations](pointer-integer-representations.md).
The historical sibling-pointer defect is not a fresh current-master finding.

Lifetime end invalidates access to the affected object/backing storage.
Destroying a descriptor does not destroy independently live external backing.
Rust moves additionally change value availability and cleanup state; those
rules cannot be inferred from C or C++ pointer behavior.

## Shared operation contract

Each frontend must justify these operations with its own checked source rules.
The kernel then applies their shared effects consistently, including at calls.

| Operation | Required evidence | Resulting effect |
| --- | --- | --- |
| Allocate storage | Checked extent/alignment and allocation kind | Fresh live storage and the specified owner; no fabricated contents |
| Select construction destination | Exact pointer, layout, range and authority | Bind that destination before execution; no extra freshness assumption |
| Begin object/subobject use | Admitted declaration or construction rule | Record/validate type and lifecycle phase; no arbitrary reinterpretation |
| Initialize scalar/field | Valid destination, conversion, phase and write permission | Store the converted value and mark the written range initialized |
| Read typed value | Valid object/access type, phase, alignment, initialized representation and read permission | Observe the value at that state |
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

## Typed and byte observations

For a supported declared uint32 at one state, byte `k` denotes bits
`8*k` through `8*k+7` of its word. Four initialized bytes determine the same
little-endian word whether written inline or by a checked modular helper.
A partial update preserves other initialized bytes; incomplete initialization
or bytes from an older state cannot determine a current complete word.
A byte array, cast, requested load width or ownership claim does not create a
uint32 object.

Typed cells, byte fragments and lazy projections describe one representation.
Overlapping stores update or invalidate observations. Joins retain only values
and initialization justified on every arm; havoc cannot revive older contents.
Pointer bytes cannot manufacture provenance. Program reads additionally require
valid access, authority and initialization: constructing a logical read term
establishes none of these. The current bounded implementation and assumptions
are in [Byte representation](../docs/internals/byte-representation.md).

The archived C++ profile separately approved the bounded implementation
contract `clang19_1_7_lp64_le_declared_uint32_bytes_v1`: Clang 19.1.7,
Linux x86-64 GNU LP64, eight-bit bytes and little-endian four-byte uint32
representation access. This was an explicit compiler-profile assumption, not a
literal C++20 guarantee or a rule for arbitrary records/scalars. The byte
aliasing exemption alone does not establish the representation-byte array
needed by pointer arithmetic. Any current/new admission must identify its
actual profile and report its assumptions; an archived marker or helper name
is not evidence of current implementation. Likewise, assumed equivalence of a
pinned standard-library model is separate from certification of the model body.

## Entry, calls and effects

Symbolic entry and actual modular calls must enforce matching native
requirements for the selected profile. Check layout, type, constness,
provenance, initialization and lifetime separately from resource permission.
A native signature or successful cell lookup cannot justify all of them.
The completed [entry/call matrix](object-model-current-audit.md#native-interface-evidence-matrix)
records the selected evidence; no particular archived `valid_place` or
`initialized` syntax is an acceptance requirement.

Proof-entry naming is observational. It must not execute a store into raw
output, initialize a constructor placeholder or assume convenient separation.
Output effects bind the actual destination and initialized portion; reassignment
of a parameter cannot redirect a promised entry-address effect. Copying and
transport use the actual call's checked separation context. Constructor
completion checks required value fields without initializing padding.
External construction assumptions remain visibly external and cannot authorize
arbitrary output-buffer initialization.

Ordinary execution, body summaries, expansion and retained checking must apply
the same laws. Changed semantic identities must invalidate incompatible
artifacts. [Aggregate construction](aggregate-construction.md) records the
implemented destination/copy/retirement contract.

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

## Acceptance and cost

The bounded milestone's pointer-field fold, entry/call matrix and exact modular
byte-output composition are checked in the current audit, including
initialization, authority, stale-state and forged-type controls. Keep these
compositions as regressions when extending a source profile. Use the named
current witnesses rather than historical example counts.

Keep lookup indexed by selected object/range and work proportional to the
explicit input and affected delta, up to indexing factors. Do not eagerly
expand objects into bytes, scan unrelated memory/facts, or rediscover an
unbounded equality set during retained checking. Changed hot paths need
multi-size deterministic scaling evidence.

The [archived design and implementation notes](https://github.com/clicklang/click/blob/2175760b9/design/cpp-object-model.md)
preserve the detailed investigation, rejected alternatives and old APIs.
Their implementation claims, feature freeze and old acceptance matrix are not
current upstream requirements.
