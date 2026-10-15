# Pointer subobject extents: closing the scalar-subobject P1

Status: approved 2026-10-15; decisions D1-D5 accepted as recommended. It targets
[the scalar-subobject bug](../bugs/pointer-arithmetic-crosses-scalar-subobject.md)
on current master. It does not revive the archived object model. It reuses that
model's semantic conclusions (`design/cpp-object-model.md` at `e3d84a785`) where they
still apply, but proposes a narrower representation.

## The hole, as it exists on master

Master `9ea01e78f` accepts every one of these (in the scratch reproductions, each
claim verifies):

| Variant | Source | Should be |
| --- | --- | --- |
| direct | `return *(&p->first + 1);` | reject the read |
| pointer local | `int32* q = &p->first; q = q + 1; return *q;` | reject the read |
| formation | `return &p->first + 2;` | reject the formation |
| modular helper | `arr(&p->first)` where `arr` has `views p[0..2]` and reads `p[1]` | reject the call |
| address equality, subobject | callee `if (q == p) return *q;` with only `views p[0..1]`; caller passes `&s->first + 1, &s->second` | reject the callee |
| address equality, whole objects | the same callee; caller passes `a + 4, b` with `views a[0..4]; views b[0..1]` | reject the callee |

The last row is not a subobject case: a one-past pointer of a separate array
reaches another object through a C-level address comparison inside a callee.
So the bug is two defects:

1. **Local (subobject extent).** The kernel never narrows a pointer to the
   member it was formed from. `&p->f` lowers to
   `AddressOf(TypedLoad{PointerOffsetBytes{p, off}, field_type})`. Formation
   (`pointer_offset_by_elements_paths`, `pointer_offset_by_bytes_paths` in
   `src/kernel/eval/operators.rs`) is checked only against held ranges
   (`held_range_membership`) or the whole block (`pointer_block_bounds`).
   Dereference (`read_c_lvalue_paths_without_ranges`, `write_c_lvalue_paths_*`)
   is checked only for address coverage by an owned or viewed range
   (`ResourceContext::permits_memory_read` / `memory_write_range`).
2. **Modular (designation across address equality).** In a callee, a pointer
   parameter is an opaque address. Authority lookup
   (`read_access_entries` through equality-graph pointer classes) accepts any
   pointer whose address is proven equal to a carrier that holds authority.
   That includes equality learned from a C `==`. In C, address equality
   does not make a one-past pointer dereferenceable.

## Principles

- **Extent is separate from authority.** Leave authority address-based and
  unchanged. Add one independent check: an access must stay inside the extent
  of the pointer that performs it. Address rewriting, aliasing and cell lookup
  never consult or alter extent.
- **Extent is carried in the value.** It is not reconstructed from addresses,
  held ranges or cell types.
- **Root extent stays as it is today.** The complete object or allocation is
  already enforced (block size, held ranges, `object_identity()`,
  `OnePastEndComparison`). The new mechanism adds only *narrowing* below the
  root.
- **No new contract syntax.** Existing resource clauses and spec equality carry
  the modular obligations (decisions D1 and D2).

## Phase A: subobject extents (local defect)

### Representation

Add `extent: PointerExtent` to `CPointerValue` (`src/kernel/primitives.rs:976`):

```rust
enum PointerExtent {
    /// No narrowing: the complete object or allocation, as enforced today.
    Root,
    /// A selected subobject in the same block, in byte offsets: [start, end).
    Subobject { start: PointerOffsetTerm, end: PointerOffsetTerm },
}
```

- Extent is part of value identity (`Eq`/`Hash`/`Ord` via `identity()`). Unlike
  `pointee_constant`, it is not ignored.
- Position is derived from the address; no separate position term is kept.
- `Root` is the default at all 35 `CPointerValue::new` sites, so landing the
  field alone changes no behavior.
- All 27 `into_pointer()` sites and 11 `replace_pointer` sites are audited.
  - A site that keeps using the value as a pointer must keep the extent.
  - Pure address uses (cells, aliasing, equality-graph keys) are correct
    to drop it.
  - The audit is a checked list in the PR.

### Producers

| Operation | Extent of result |
| --- | --- |
| Member selection `&p->f`, `&s.f` (C), member address (C++ `lower_place`/`CheckedObjectAddress`) | `Subobject[off, off + sizeof(f))` relative to the containing address. `f` may be a scalar, a nested record or an array member. |
| Array member decay `p->arr`, `&p->arr[i]` | the member array's extent (the whole `arr`, not the element) |
| Element of an array of records `items[i].y` | `y`'s extent within element `i` |
| Address of a declared object `&x`, array decay, `malloc`, string literal | `Root` (already exact: the block is the object) |
| Typed pointer arithmetic `q + n`, `q - n`, `&q[n]` | same extent as `q` |
| Copy, local assignment, argument binding, return | same extent |
| Store to memory, then reload of that exact cell | same extent: cached `CValue::Pointer` cells already return the stored value. The `pointer_read_stored_value` family in `memory_provenance.rs` must return the whole `CPointerValue`, not `Pointer`. |
| Reload of an unknown cell, havoc, modular result | `Root` (today's behavior; Phase B covers what can still go wrong) |
| Cast to a non-character object pointer type | same extent (a cast neither narrows nor widens; D3) |
| Cast to `void*`, `char*`, `unsigned char*` | `Root` (byte view of the enclosing object; keeps `container_of`, D4) |

The frontend already knows each field's type and size when it forms
`&p->field` (`resolve_field_access`, `C0StructField.byte_width`). Today it lowers
the member to a bare `PointerOffsetBytes{pointer, bytes}`. Phase A replaces that
for members with `CExpression::MemberAddress{pointer, offset, width}`, or an
optional `member_width` on `PointerOffsetBytes`, so the kernel learns the
extent. Rust has no raw pointers yet (`rust/charon.rs:485`), and its slice
indexing already asserts `index < length`. Record in the docs that safe-Rust
borrows never justify raw arithmetic, once raw pointers exist.

### Consumers

| Operation | Added check for `Subobject[s, e)` (none for `Root`) |
| --- | --- |
| Pointer formation (`pointer_offset_by_*_paths`) | `s <= result <= e` (one-past allowed) |
| Typed read or write of `w` bytes (`read_c_lvalue_paths_without_ranges`, `write_c_lvalue_paths_for_initialization`, `CheckedObjectAddress`) | `s <= addr` and `addr + w <= e` |
| Pointer subtraction / relational comparison | both operands have equal extents, in addition to today's same-object rule |
| C `==` / `!=` | unchanged (address comparison) |

Each check is two offset comparisons in the same block, decided by the existing
difference reasoning. That cost is constant per operation, independent of
unrelated state, as the
[efficiency contract](../docs/internals/verification-efficiency.md) requires.
A failure is reported as `pointer arithmetic left the pointed-to subobject` or
`read outside the pointed-to subobject`, naming the member's extent.

### Modular extent at calls (resource clauses as extent claims, D1)

At a call, each pointer argument with a `Subobject` extent must cover every
range that the callee's resource clauses name through that parameter.
`views p[0..2]` against `&s->first` requires `[p, p+8) ⊆ [first, first+4)`,
which fails, so the `caller` variant is rejected. Resource clauses already name
the carrier and range, so this needs no new syntax and only reads the clauses of
the selected callee. The callee assumes nothing new, so its proofs are unaffected.

The same check applies when folding a resource predicate whose body clause
names a `Subobject` pointer. This keeps
`fold(list(&s->node))` from claiming more than the member provides.

### What Phase A closes

direct, pointer local, formation, modular helper, and pointer-field store/reload
within one function (the extent travels with the stored `CValue`). It does not
close the two address-equality rows.

### Status after step 2

Delivered:
- `CExpression::Subobject { pointer, width }`, emitted by the C frontend for
  struct members and by C++ member-address lowering. Union members are not
  narrowed.
- Memory lvalues carry the extent, so `&*q` and `&q[i]` keep it.
- Formation and access are checked against the extent
  (`pointer arithmetic left the pointed-to object`,
  `access outside the subobject the pointer designates`).
- Loop abstraction keeps a pointer local's extent, and the back edge refuses
  a body that changes it.

Known limits, each refused or unchanged rather than accepted unsoundly:
- A loop that moves a pointer between different subobjects is refused at the
  back edge. Invariants cannot yet state which subobject a pointer
  designates.
- Pointers read from cells a call or loop havocs, and pointers loaded at
  function entry (including a static pointer's initial value), have no
  extent. That is the modular case Phase B covers.
- Contracts observe member addresses without narrowing, and spec pointer
  equality is still address equality until Phase B.

### Status after step 3

A memory clause's range must lie inside the extent of the pointer that names
it, wherever the clause is evaluated: a call's requirements and results, a
composite body when it is expanded, folded or unfolded, and loop effect
clauses. The kernel checks it where a clause's base value becomes a range
(`segment_extent_refusal`); fold lowering refuses constant ranges by name
first. A pointer without an extent is unaffected.

## Phase B: designation is part of the pointer value (modular defect)

Approved 2026-10-15 in place of the earlier "two equalities" proposal.

### Principle

A C pointer value is an address plus the object it designates. C `==` on
pointers compares addresses only: `&pair.first + 1 == &pair.second` holds,
and only the second may be read through.

- **Addresses stay where they are.** The kernel's `Pointer` (block and offset)
  is the address. The equality graph keeps merging addresses with full
  congruence, whatever the source of the equality, including C `==`. Cells,
  aliasing, stored values, ordering, branch decisions and `return q == p` keep
  working unchanged. No equality is hidden from any part of the system.
- **Designation is a separate component of the value.** Read and write
  permission depends on the designation as well as the address. An address
  equality says nothing about designations, so it cannot carry permission from
  one designation to another.

### Why the address cannot carry it

Measured on master `5fa772724`. Inside `if (q == p)`, Click respells the local
`q` to `p`'s address. A permission check derived from the accessed address,
even through `Pointer::object_identity()`, therefore sees only `p`, and the
hole stays open. The designation must live on the value and survive
respelling, as the Phase A extent does.

### Representation

- **Values.** `CPointerValue` carries a designation: a root token and the
  Phase A extent.
  - The token is the allocation or declared object for a pointer formed from
    one.
  - A parameter, a pointer loaded from memory, and a call result each get an
    opaque token, minted once at the point the value enters.
  - Respelling the address (`replace_pointer`) keeps the designation;
    substitution maps it like the extent's start.
- **Ranges.** A memory range named by a clause records the designation of the
  pointer value that named it, at the point the clause becomes a range
  (`evaluate_loop_effect_segment` and the fold lowering, as for extents).
  Splitting and joining a range keep the designation.

### Rule

A read or write through a value is permitted by a held range only when
both of these hold:
- the range covers the address, as today;
- the value's designation is the range's designation, or the two are related
  by a designation equality.

Designation equalities come only from value-level sources:
- contract `==` on pointers (`requires`, `ensures`, invariants);
- a pointer read back from memory and the value stored there;
- resource argument binding at fold and unfold;
- copies and pointer arithmetic, which keep the designation by construction.

A missing source makes Click refuse a valid proof, the safe direction. The
corpus measurement after each step finds those sources.

### Contract `==`

D2 applies. At a call the caller must establish a precondition `p == q`
between pointers for their designations too. Member addresses written in
contracts carry the member's extent, as program member addresses do. The
callee adopts the designation a precondition equality states at entry. This
closes the remaining entry case: a global initialized to `&g.first` that a
callee steps past.

### Steps

1. Designation tokens on values and ranges, with no behavior change.
2. Enforce the rule at reads and writes, with the contract, stored-value and
   binding sources. Measure the corpus and add any missing source.
3. Designation-aware contract `==` (D2) and contract member narrowing.

The `docs/concepts/memory-model.md` sentence "two addresses are equal exactly
when their pointers are equal" becomes: equal addresses name the same memory,
not the same pointer value.

### Measurement before step 1

Hiding C pointer `==` from the verifier entirely broke 26 mdtests and two
examples (`modeled-binary-tree`, `rbtree-augmented`). Every failure was about
the comparison's value, and none was about permission. That cost does not
apply to this design, because address knowledge is kept. The proofs at risk
are those that read through one designation with another's permission,
related only by an address fact. The measurement found none outside the
reproductions.

## Decisions (approved as recommended)

- **D1. Resource clauses double as extent claims at calls and folds.**
  - Recommended: yes. There's no new syntax, and the meaning matches
    intent: `views p[0..2]` already says "p has two readable elements".
  - Alternative: a separate `valid(p[0..n])` clause. The archive's
    `valid_place` surface showed the migration cost.
- **D2. Spec `==` on pointers means value equality (address and extent).**
  - Recommended: yes. `address(p) == address(q)` remains for address-only
    claims.
  - Without it, Phase B cannot be sound without new syntax.
- **D3. Non-character casts keep extent but do not narrow.**
  - `((int32*)pair)[1]` on a `struct Pair*` stays accepted, because the
    struct's root extent covers both members.
  - Strict C makes `(int*)pair` designate `pair.first`.
  - Recommended: accept for now and track it as a follow-up. Narrowing on
    struct-to-first-member conversion is possible, but layout-dependent.
- **D4. Character and `void` casts widen to `Root`.**
  - This keeps the Linux `container_of` in `examples/rbtree-augmented` and
    `mdtests/c_container_of.md` (`(void*)member - offsetof(...)`, then a cast to
    the enclosing type). It also keeps `memcpy` byte views
    (`examples/byte-representation`).
  - The consequence: `*(int32*)((char*)&p->first + 4)` is accepted. An explicit
    character round trip is the standard escape hatch, and compilers honor it.
  - Recommended: accept, and document it in `docs/`.
- **D5. Staging.**
  - Recommended: Phase A in three PRs:
    1. the carrier with `Root` everywhere, as a no-behavior-change audit;
    2. producers and consumers in C and C++, closing the local variants;
    3. the call/fold extent checks.
  - Phase B follows as its own design-confirmed PR.
  - The bug file stays open, with the remaining rows updated, until Phase B
    lands.

## Validation

- Keep the original reproduction (direct) and every row above as mdtests,
  unchanged C:
  - negative fixtures for each rejected variant;
  - positive controls for `*(&p->first + 0)`, `&p->first + 1` formation without
    a dereference, `*(&p->second)`, member-array traversal, `container_of`,
    and `memcpy` byte views.
- Expected fixture churn: `a_loop_writing_past_a_sibling_field_forgets_the_union_view.md`
  (`p = &source.tag; p[2] = 9;`) changes from a refuted claim to a rejected
  store. Its C stays unchanged, and its expectation moves to the new refusal.
- Run all 52 example projects and the full mdtest corpus after each Phase A
  step. Any newly failing example is investigated, not adapted: either it
  relies on sibling traversal (a real finding to report) or the extent was lost
  in transport (a Phase A bug).
- Ordinary, expanded, rewritten and retained checking agree for the new
  fixtures (`click audit` on each).
- Scaling: a multi-size regression showing formation and access step work
  constant in the number of live subobject pointers.
