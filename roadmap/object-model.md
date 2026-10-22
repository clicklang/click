# P2: Stabilize and deliver the shared object model

Priority: P2.

Soundness: soundness-adjacent. This work changes the evidence used to justify
object access, pointer designation, initialization and modular transfer across
C, C++ and Rust. No new false acceptance is known. Reproduced soundness defects
keep their own P1 bugs and must be repaired or refused before affected support
is claimed.

## Goal

Land the accepted bounded object model on upstream master as independently
reviewable, green slices, taken from the archived implementation of
[PR #646](https://github.com/clicklang/click/pull/646). New C++ feature
admission stays frozen until this foundation lands. Done means a checked model
with demonstrated language boundaries and preserved existing behavior.

- Laws and operation audit: [C++ object model and shared memory semantics](https://github.com/lacker/click/blob/e3d84a785792c007da19d2f42d75b9e143372164/design/cpp-object-model.md).
- Construction/return protocol: [aggregate construction](../design/aggregate-construction.md).
- Subobject pointers: [subobject extents](../design/pointer-subobject-extents.md).
- Revisions, commands, failure ledger, change inventory and the record of
  every landed extraction: [recovery audit](../design/object-model-recovery-audit.md).
  Record new results there, not here.
- Later C++ coverage belongs to [cpp-support.md](cpp-support.md).

## Where it stands

- The implementation lives on the preserved recovery branch in the fork. Its
  normal example audit passes 50 of 52 projects; arena (destroy) and
  binary-tree fail. Nothing from it is activated upstream.
- Upstream has landed the independent extractions recorded in the audit. These
  include pointer-read naming: every pointer read is named by the read itself,
  and its value and designation are compared under one rule
  ([#1806](https://github.com/clicklang/click/pull/1806)).
- Pointer-designation changes upstream (#1245) broke rbtree proofs that
  verified before. They run in the nightly examples, not the gate. See
  [below](#rbtree-regressions-on-master).

## What's left

### Recovery failures

- [ ] Arena: the destroy proof and the occupancy postcondition of arena-write.
- [ ] Binary-tree.
- [ ] Attribute each remaining failure to its introducing change and record it
  in the audit's failure ledger.

### Shared foundation

These are groups of work to account for, not one PR each. The audit's
dependency inventory decides which parts land independently and which must
land together. Credit mechanisms that already landed when they satisfy a law.

- [ ] **Operation and evidence audit:** storage, layout/type, domain,
  lifecycle, initialization and authority evidence for every admitted
  operation: declarations, construction, copying, moves, typed/byte reads and
  writes, casts, havoc, branch joins, cleanup and lifetime end.
- [ ] **Object/storage and construction:** coherent layout/subobject evidence,
  destination binding, construction completion and retirement. Preserve C
  aggregate returns and Rust construction; keep bounded C++ copy-equivalence
  admission and exact destination checks.
- [ ] **Initialization and observations:** preserve unknown initialized values,
  compressed initialized ranges and explicit output effects. The uint32
  typed/byte bridge describes one value at one snapshot; partial writes update
  only their bytes; a no-op writer establishes no new output.
- [ ] **Pointer designation and transport:** pointer reads are done (#1806).
  Remaining: retain complete pointer evidence through arithmetic, casts, calls,
  resources and substitutions; reject cross-subobject access, unjustified array
  traversal, one-past dereference and expired objects.
- [ ] **Entry, resources and modular calls:** assume explicit input promises at
  symbolic entry and check them at actual calls and resource creation. Preserve
  aggregate/pointer values, conditional bodies, mutable descriptor bindings,
  returned initialization and the caller's frame.
- [ ] **Frontend activation:** enable each language/profile only after its
  dependencies and positive/negative call controls pass. Unsupported cases get
  bounded, specific refusals. C sources must not acquire C++ requirements.
- [ ] **Proof and performance parity:** recheck ordinary, expanded, rewritten
  and retained proofs. Protect local operations with deterministic multi-size
  scaling tests; no global scans per step and no raised limits.

If pointer representation, equality, transport and access checks depend on one
another for soundness, land that closure together rather than exposing an
intermediate model.

### rbtree regressions on master

- [ ] [rbtree-augmented sized resources](../bugs/rbtree-augmented-sized-resources-lack-the-parent-pointer-fact.md):
  26 of 64 sidecars fail on master.
- [ ] [rbtree_insert Top arm](../bugs/rbtree-insert-top-arm-contradiction-refused.md).
- [ ] [rbtree-erase `flips_red_all`](../bugs/rbtree-erase-flips-red-all-loop-refused.md).
- [ ] [rbtree_size_rotate_model fold](../bugs/rbtree-size-rotate-model-fold-lacks-complete-instance-body.md).
- [ ] Move one fast rbtree-augmented sidecar into the gate so a kernel change
  cannot break the directory unseen.

### Acceptance

- [ ] Every compatibility group has a classification and every regression
  from a delivered slice is resolved:

  | Group | Reproduction |
  | --- | --- |
  | Pointer-field frames and stored values | owned-vector and owned-string projects |
  | Nullable allocated resource bodies | [conditional allocated record](../mdtests/conditional_allocated_record_output.md); allocated-linked-list, heap-object |
  | Borrowed/owned buffer and cursor transfer | arena, detachable-buffer, owned-segmented-buffer, owned-split-buffer, input-cursor, binary-tree, concurrency-fork-join, multifile-registry, ring-buffer |
  | Other C proofs | refcount, rbtree-augmented |
  | Rust availability/ranges and proof cost | rust-chunks-exact, rust-byte-sum |
  | Importer and proof scaling | record-inventory multi-size work, growing-place graph test, decoder audits |

- [ ] The [bounded acceptance matrix](https://github.com/lacker/click/blob/e3d84a785792c007da19d2f42d75b9e143372164/design/cpp-object-model.md#stabilization-work-and-exit-criteria)
  has named evidence for representation, modular transfer, destination/copy,
  aliasing/frames, lifetime/availability, typed access, proof modes and scaling.
- [ ] The unchanged pinned Bitcoin `ser_readdata32` verifies with exact word
  value, initialization, span bounds and backing lifetime, in modular,
  expanded and retained checks.
- [ ] The [entry-count cell fixture](../mdtests/resource_uint64_entry_cell_fold.md)
  and its [wrong-index counterpart](../mdtests/resource_uint64_entry_cell_fold_wrong_index.md)
  keep passing and failing, and a view-only counterpart rejects the write.
- [ ] The design docs' implementation claims match upstream, and the next C++
  work moves back to `cpp-support.md`.

## Accepted design

Retain typed cells, allocation identities, immutable snapshots and indexed
resource ranges. Execution, logical observation and modular proofs share
operations and checked evidence. Frontends supply explicit language rules and
authenticated source metadata; source spelling or matching numeric addresses
cannot manufacture semantic evidence.

| Component | Meaning | Does not imply |
| --- | --- | --- |
| Storage | Allocation identity/generation, live extent and alignment | An object of the requested type |
| Object and place | Admitted type, containing object, subobject or array domain, lifecycle phase | Initialization or access authority |
| Pointer value | Address plus designation, position and lifetime evidence | Permission to read or write its referent |
| Representation | Typed values and byte observations of one object at one snapshot | Legality of every access type |
| Initialization and value | Initialized bytes, available value, language value validity | Ownership or a particular value |
| Authority | Checked ownership, view or loan for the footprint | Object creation, initialization or pointer origin |

- Unknown-initialized and uninitialized contents stay distinct. Forgetting a
  value keeps initialization and object identity; joins keep only justified
  common guarantees.
- Address equality supports alias and frame reasoning; it is not pointer
  identity or typed-place validity.
- `valid_place(p)` and `valid_place(p[0..n])` state typed-place validity and
  grant neither ownership nor initialization. A view alone does not assert
  that storage holds an object of a requested type.
- Initialization effects are explicit, body-checked postconditions.
  Mentioning an output read in a proposition does not initialize it.
- Construction uses the exact caller-selected destination. Allocation,
  construction completion, copying and lifetime end are distinct operations;
  construction implies neither freshness nor separation.

Language boundaries:

- **C:** keep the explicit allocated-storage/effective-access rules and the
  ordinary C verification boundary. C++ object requirements do not activate
  because the C frontend knows a struct layout.
- **C++:** native references, declarations and checked importer identities
  supply place evidence. A native signature's promise is checked at actual
  calls as well as assumed at body entry. The profile is pinned Clang 19.1.7,
  C++20, `x86_64-unknown-linux-gnu`, LP64, little-endian; the uint32
  representation guarantee is the named assumption
  `clang19_1_7_lp64_le_declared_uint32_bytes_v1`.
- **Rust:** reuse shared storage, initialization, representation and transfer,
  keeping move availability, drop and borrowing explicit.

## Out of scope

Placement construction and storage reuse, overlapping unions, general
inheritance and virtual dispatch, broader exceptional construction, arbitrary
owning containers, concurrency, additional target profiles, and full contracts
for integer-carried pointer origins. Ask for a design decision only when a
concrete case would change an accepted source-language promise, choose a new
compiler guarantee or contract surface, or enlarge the bounded profile.
