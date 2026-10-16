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
  extent. A caller that formed such a pointer checks it against the callee's
  clauses at the call (step 3).
- A C pointer comparison still states pointer equality until Phase B.

### Status after step 3

A memory clause's range must lie inside the extent of the pointer that names
it, wherever the clause is evaluated: a call's requirements and results, a
composite body when it is expanded, folded or unfolded, and loop effect
clauses. The kernel checks it where a clause's base value becomes a range
(`segment_extent_refusal`); fold lowering refuses constant ranges by name
first. A pointer without an extent is unaffected.

A contract `==` between two pointers that both carry an extent also requires
the extents to be equal (D2), so a call cannot satisfy `requires q == p` with
`&pair->first + 1` and `&pair->second`. When either value has none, the
comparison stays an address equality: that value's designation may be
unknown, and assuming the equality must not refute a reachable path. A
contract's scalar member address `&p->f` is narrowed to the member as the C
frontend narrows it, so `ensures result == &p->second` does not hold for
`&p->first + 1`. Member loads and other contract spellings of member places
are not narrowed.

## Phase B: C `==` states address equality (modular defect)

Approved 2026-10-15. It replaces the earlier "designation is part of the
pointer value" plan, which is parked (see *Abandoned approach* below).

### Principle

C `==` on pointers compares addresses: `&pair.first + 1 == &pair.second`
holds, and only the second may be read through. So a C comparison should
tell the verifier exactly that, and no more:

- C `p == q` and `p != q` between object pointers state
  `address(p) == address(q)`, an equality of two `uint64` values. They do not
  state the kernel's pointer equality.
- Contract `==` between pointers keeps its meaning: the two are the same
  pointer value. `address(p) == address(q)` stays the spelling for an
  address-only claim.
- An address equality never becomes a pointer equality. Read and write
  permission follows pointer equalities, so `if (q == p) return *q;` cannot
  borrow `p`'s permission for `q`.

Equal things still behave the same way: equal addresses are equal integers,
and equal pointers are equal everywhere. Only the C comparison's claim is
narrowed to what C guarantees.

### What stays a pointer equality

Pointer equalities still come from value-level sources: contract `==`,
copies and pointer arithmetic over equal terms, a load and the value stored
in its cell, and resource argument binding. A comparison with the null
pointer constant is unchanged: C guarantees that a pointer equal to null is
null.

### Steps

1. Lower C pointer `==`/`!=` (except against null) to address equality, and
   stop deriving pointer equality from address equality.
2. Update the proofs that used a C comparison to conclude pointer equality.
   Each either states the address claim with `address(...)`, or relies on a
   value-level source. Add the two address-equality rows of the hole table as
   regressions.
3. Load congruence over address equality. Reads of one memory at equal
   addresses read one cell, so they are equal values; that grants no
   permission. Done: the equality graph keys every read by its snapshot and
   numeric address (see `docs/internals/equality-closure.md`), and
   `mdtests/pointer_loads_equal_after_late_address_equality.md` passes again,
   with a displaced-field variant beside it.

Measured with steps 1 and 2 on master `979df5bbd`: three mdtests and one
example needed changes. `model_identity_pointer_payload`,
`loop_old_parameter_resource_argument` and `examples/modeled-binary-tree` now
compare addresses where their C does; the reads fixture waited on step 3.

### Abandoned approach

The earlier plan kept C `==` as pointer equality and added a separate
same-object condition, so that contract `==` meant "same address and same
object". It is parked on branch `claude/dreamy-darwin-2kvqba-same-object-wip`.
It needed the object to travel through every tactic, rewrite, load, loop and
memory transport, and it still left two mdtests and two examples failing on
reads of one cell across snapshots. Narrowing the C comparison itself needs
none of that.

## Phase C: pointers of unseen formation

Status: approved 2026-10-16; decisions E1-E3 accepted as recommended. Step 1
and the evidence infrastructure of step 2 are delivered; no producer assigns
an opaque extent yet (see *Evidence as built*).

### The hole

Today a value without an extent means two different things. A pointer the
function formed from a declared object, an allocation or a string literal
is bounded by its complete object, and that bound is exact. A pointer whose
formation the function never saw also has no extent: a parameter, a pointer
loaded from memory at entry, a call result, or a pointer reloaded from a
cell a call or loop havocs. Its actual designation may be a single member.
Neither kind is checked against an extent, and authority stays
address-based, so the second kind can step past its member and read a
sibling with permission held through another pointer at the same address.
[The bug file](../bugs/pointer-arithmetic-crosses-scalar-subobject.md#pointers-of-unseen-formation)
has two complete programs that verify on master: a callee steps a pointer
field its caller set to `&p->first`, and a callee reads through a parameter
its caller formed as `&p->first + 1`. In both, the contract states the
designation exactly (`requires h->link == &p->first`), but the comparison
stays an address equality because one side has no extent.

### Principle

Every pointer value has a designation. A pointer of unseen formation gets
a fresh **symbolic extent**: its start and width are new variables, and
accesses and arithmetic through it are checked against them exactly as
against a member's extent. Only facts can prove such a check, and the facts
come from what the contract already says:

1. **Memory clauses (D1, callee side).** A clause naming a range through a
   pointer value claims the pointer designates that range. At a call this
   is the caller's obligation today (`segment_extent_refusal`). Where the
   same clause is assumed (function entry, a call's results, an unfold), it
   adds the fact that the range lies inside the pointer's extent.
   `views p->second` through a `struct Pair* p` covers `p`'s bytes 4 to 8,
   which is what narrowing `p` to `second` needs.
2. **Pointer equality (D2).** A contract `v == w` between two values with
   extents already requires equal starts and widths (#1241). With symbolic
   extents it pins the unknown one to the known one. `requires
   h->link == &p->first` then tells the callee that `h->link` designates
   `first`, and `*(h->link + 1)` is refused.
3. **Nothing from the type.** A `T*` does not designate a `T`: a one-past
   pointer has the same type.

A pointer the function forms itself keeps today's exact extent, or none
when it is a complete object. Equalities between two symbolic extents
relate their variables, so `requires q == p` with `views p[0..2]` still
lets the callee read `q[1]`.

### Representation and cost

`SubobjectExtent::width` becomes a term; constant widths are the existing
case. The guards in `subobject_extent_guards` already compare the access
against `start` and `width`, and `pointer_access_in_range` decides them
from facts when they are not constant. Coverage facts are ordinary pure
facts over the extent's own variables, added once per assumed clause, so
each check stays a local decision with no scan of unrelated pointers.

### Steps

1. Width as a term, constant everywhere: no behavior change. Done:
   `SubobjectExtent::width` is a `Bitvector32Term`. A consumer that still
   needs a constant (an unsigned 64-bit clause range, the refusal's byte
   count) treats an unknown width as not proven. Substitution and variable
   collection map only `start`; step 2 extends them to the width when it
   first carries variables.
2. Symbolic extents for parameters and pointers loaded at entry, with
   coverage from entry clauses. Add the bug's two programs as rejected
   fixtures and run the full corpus; investigate each new failure as either
   reliance on an unstated designation (a finding) or a lost fact (a bug).
   The evidence infrastructure is delivered without a producer. Activating
   parameters alone regressed valid programs whose authority is named
   through model payloads, loaded pointers or loop-reassigned locals, which
   have no extent yet, so activation lands with step 3.
3. Call results, havocked reloads, model payload pointers and loop-carried
   values. A loop-carried local the body reassigns from a load gets a fresh
   opaque extent at the head instead of keeping its entry extent.
4. C++ references and pointers; documentation.

### Evidence as built

A pointer of unseen formation carries `SubobjectExtent::opaque(v)`: a
symbolic start and width named by one variable from a reserved range. What it
covers is known only from evidence:

- **Tagged held ranges.** A memory range evaluated from a clause records the
  opaque extents its pointer makes claims about (`CMemoryRange::designations`):
  its own, and, for a member pointer, the one it selected the member of.
  The tag is not part of the range's identity. Splits keep it, a join keeps
  only a tag both pieces carry, and a range that loses it only loses
  evidence. An access through an opaque extent, and a clause naming a range
  through one, must lie inside a held range carrying that extent's tag, or
  the tag of an extent a pointer equality identified with it.
- **Equalities.** A contract `==` between an opaque and a constant extent
  records that the opaque one covers the constant one's bytes
  (`__click_subobject_covers_*`, indexed by the extent's pointer class); two
  opaque extents are identified by their starts and widths.
- **Assume sites.** A function's own entry requirements and clauses, opening
  or unfolding a held composite and a held population control are evaluated
  under `PureFactContext::assume_entry_clause_extents`: the clause was
  checked where it was established, so it is not checked again and its
  ranges become evidence. Every other evaluation checks.

Diagnostics keep their order. An access with no authority at all, or a call
clause no held range could supply, is left to the permission check or the
transfer, which name the missing resource; only an access or clause the
context could otherwise perform is refused for its designation. Pointer
arithmetic through an opaque extent is not checked; accesses through the
result are.

### Decisions

- **E1. Parameters get symbolic extents, not only loaded pointers.**
  Recommended: yes. The parameter program above needs it.
- **E2. A struct pointer used with `->` does not imply one complete
  struct.** Recommended: yes, rely on clauses. The alternative assumes
  `sizeof(T)` bytes whenever the body selects a member, which a one-past
  `struct T*` violates.
- **E3. Width as a term rather than a separate "unknown extent" variant.**
  Recommended: a term. Equalities and coverage facts then work on one kind
  of extent, and constant widths need no special case.

## Decisions (approved as recommended)

- **D1. Resource clauses double as extent claims at calls and folds.**
  - Recommended: yes. There's no new syntax, and the meaning matches
    intent: `views p[0..2]` already says "p has two readable elements".
  - Alternative: a separate `valid(p[0..n])` clause. The archive's
    `valid_place` surface showed the migration cost.
- **D2. Spec `==` on pointers means value equality (address and extent).**
  - Recommended: yes. `address(p) == address(q)` remains for address-only
    claims.
  - Phase B keeps this meaning by narrowing the C comparison instead.
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
  - Phase B follows as its own PRs.
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
