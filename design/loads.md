# Pointers, loads and stores

Status: approved (2026-11-23). Steps 0, 1, 2 and 3a-i of the migration, and
PRs 1 and 2 of step 3b, are implemented; the rest is not.

## Scope

Three things carry every C, C++ and Rust memory operation the kernel reasons
about:

| Thing | Kind | What it is |
|---|---|---|
| **pointer** | value term | an address and a provenance (`design/pointer-model.md`) |
| **load** | value term | the bytes of a cell at a version point |
| **store** | memory event | a recorded step that writes a cell's bytes |

Below them are program points, which say what a version point is and how
stores are recorded (`design/point-named-reads.md`, `design/exact-reads.md`).
This design defines loads and stores, and how pointers use them.

"Read" stays the general word for anything that observes state: a local, a
binder, a resource field, `old(..)`. A **load** is the specific operation on
memory, as in Click's `load<T>(address)`, MiniRust and LLVM. A **pointer load**
is a load decoded at a pointer type.

## Problem

A value loaded from memory has six encodings today, each with its own identity,
store lookup and raising:

1. `MachineTerm::MemoryLoad(point, address, LoadKind)`, with fourteen kinds:
   every integer width and signedness, `Bits64`, both floats and
   `Abstract(T)`.
2. `AlgebraicTermNode::MemoryLoad`, for specification values held in memory.
3. `KernelTermNode::MemoryLoad`, the shared mirror.
4. `AddressBase::LoadedPointer(PointerLoadId)`, for pointer loads, with
   `(point, cell, value type)` in a side table, `POINTER_LOAD_REGISTRY`. The
   type is in the key, so loading one cell through `int *` and through
   `char *` gives two pointer values, and a store at one pointer type does
   not answer a load at another.
5. Load variables (`LOAD_VARIABLE_REGISTRY`), for some integer loads and, as
   `FunctionSymbolic(var)`, for function-pointer loads. No admitted fact holds
   one (census `report_load_variables_in_facts`, 6,024 C mdtests).
6. `Address::loaded_value(memory, cell)`, a pointer load named by a memory
   state's unchanged-bytes source.

Each new type needs its own copy of this machinery, and each change to one
copy is a change of identity for the others.

## The model

C, C++ and Rust define a load the same way. An object's content is its
**object representation**, a sequence of bytes, and an access at type `T`
**interprets** those bytes as a `T` (C11 6.2.6; C++ [basic.types.general];
MiniRust's typed load: load bytes, then decode at `T` against `T`'s validity
invariant). Which `T` an access may use is restricted (C effective types, C++
strict aliasing, Rust validity), but the bytes do not depend on it.

So:

- **A load is bytes.** `Load { point, cell }`, where `cell` is an address and a
  size in bytes. Its identity is the version point and the cell, and nothing
  else.
- **A value is a decoding.** `decode<T>(load)` is the load's value at `T`. The
  type belongs to the decoding, never to the load.
- **A store writes bytes.** A store of a value `v` at type `T` writes
  `encode<T>(v)` to a cell of `sizeof(T)` bytes, and gives that cell a new
  version point.

The pointer model's rule, "types belong to terms, not values", is this rule
for pointers: one cell's bytes at one version point are one pointer value,
whatever pointer type decodes them.

## Generic reasoning

Everything about loads and stores that does not interpret bytes is written once,
on cells, for every type:

| Reasoning | Rule |
|---|---|
| version selection | `ProgramPoint::read_version` chooses the point a load names (`point-named-reads.md`) |
| identity | two loads are one term when their version points and cells are equal |
| read-over-write | a load of exactly the cell a store wrote, at that store's version, is the store's bytes; this is `read_version`'s held-value and indexed-write steps (`point-named-reads.md`, P1 steps 1 and 2), not a third mechanism |
| overlap | a store that writes part of a cell, or overlaps it, ends the cell's version and answers no load of it |
| framing | a store, call or loop step proven not to write a cell leaves its version unchanged |
| separation | whether two cells can overlap, from their addresses and provenance |
| permission | owning a byte range authorizes loads and stores within it (`MemoryRange`, already type-free) |

## Per-type reasoning

Each type contributes one entry, and nothing else:

| Entry | Meaning |
|---|---|
| `encode<T>` | the bytes a store of a `T` writes |
| `decode<T>` | the value bytes have at `T` |
| validity | when `decode<T>` is defined: initialized bytes; `bool` 0 or 1; a valid enum tag; a non-null, aligned reference |
| conversions | how two decodings of one load relate: sign casts between integer formats of one width, bit-casts between integer and float |
| access | which `T` a load or store through a given lvalue may use (C effective types, C++ strict aliasing) |

The rule that joins the two halves is generic:

> A load whose version is a store of `v` at `T`, of exactly the cell that store
> wrote, decodes at `T` to `v`.

At another type `U` it decodes to `decode<U>(encode<T>(v))`, which the
conversions entry relates to `v` where one exists (the 8-bit sign cast,
a float bit-cast) and which is otherwise just that term.

Conversions are rewrites in checking, keyed by the two formats: the equality
graph relates `decode<int8>(l)` and `decode<uint8>(l)` by the sign cast with
no fact for a proof to find, as the `int8`/`uint8` load equality is free
today. Lowering may build a decoding at each format, which depends only on
types and so is fact-stable; it never folds the conversion.

Every cross-format decoding raises (`docs/internals/raise-lower-principle.md`):

| Decoding | Surface |
|---|---|
| `decode<U>(encode<T>(v))`, integers of one width | the C conversion `(U) v`, exact at equal width |
| `decode<U>(encode<T>(v))`, integer and float of one width | a bit-cast form, to be added before floats join step 3b |
| a pointer's bytes decoded as an integer, or the reverse | not supported until abstract bytes (step 5) |

### Integers and floats

`decode<int8>` and `decode<uint8>` of one byte are -1 and 255 for `0xFF`; the
sign cast relates them. Signedness is therefore part of the decoding, not of
the load.

This resolves an inconsistency in the current kinds. Today 8-, 16-, 32- and
128-bit loads carry signedness in their `LoadKind`, so the `int8` and `uint8`
loads of a byte are two terms (maintainer direction, 2026-10-30, stated at
`MachineTerm::memory_read`), while signed and unsigned 64-bit loads share
`Bits64`, one term with signedness at the use
(`docs/concepts/memory-model.md`). Under this model every width is like
`Bits64`: one load, decoded at each format. The 2026-10-30 direction's
substance, that the two values are different terms related by the sign cast,
still holds: they are two decodings of one load.

### Pointers

`decode<T *>(load)` is the stored pointer, with its provenance and array
object. When no store answers the load, it is an opaque pointer whose address
base and provenance are both named by the load.

- Every object-pointer type decodes the same bytes to the same pointer value.
  A member's bounds are bytes (`SubobjectBounds`), independent of the pointee
  type, so they stay valid at any object-pointer type.
- A function-pointer load decodes to the function the store wrote. Decoding an
  object pointer's bytes as a function pointer, or the reverse, has no stored
  value to return.
- The pointer term itself is untyped (`pointer-model.md`, "Types belong to
  terms, not values"): the type is the decoding's, `decode<T *>`, and the
  decodings at every object-pointer type are one pointer.

### Aggregates and abstract values

A struct is decoded member by member: each member is `decode<M>` of a
sub-cell. This is what lowering already does when it copies a struct field by
field; the model names it. `Abstract(T)` is the decoding of `sizeof(T)` bytes
at an abstract type, whose value the kernel treats as opaque.

## Terms

- **`Load { point, cell }`**, one Rust type, interned. It is the identity of
  every load, of every type. `point` is the selection, not a bare point id:
  identity is its `read_key()` (`Memory`, `Point` or `View`) and the cell, so
  a memory-named load is expressible until the legacy walk goes. Interning is
  keyed by `(read_key, cell)`, never by the whole `ProgramPoint`, whose
  `IndexedWrite` selection holds a derivation.
- **Integer and float values** are `decode<format>(load)`. Today that is
  `MachineTerm::MemoryLoad(point, address, kind)`, built only by
  `MachineTerm::read_named` and `MachineTerm::memory_read` (enforced by
  `build_support/read_construction.rs`). Since step 3a-i its identity is the
  interned load plus its kind, `MemoryLoad(ReadPoint, LoadCell, LoadKind)`;
  step 3b makes the kind a format.
- **Pointer values** have address base `AddressBase::Load(load)`, replacing
  `LoadedPointer(PointerLoadId)` and the side table. A pointer-side
  constructor gets the same ratchet.
- **Function-pointer values** use the same base, replacing load variables.
- **`Address::loaded_value`** is a memory-named load (`ReadKey::Memory`); it
  goes with the legacy walk.

## Calls are stores

A call writes memory too. Its effect on a cell is a store event like any
other, recorded at the call's program point:

- a cell the contract does not let the callee write keeps its version (framing);
- a cell the contract states the exit value of is a store of that value, at the
  cell's type, at the call;
- a cell the callee may write without a stated value is a store of an unknown
  value, at the call;
- a result the contract states as an entry value, `result == old(*o)`, is the
  load of `*o` at the call's entry point, the same term the caller holds.

So `ensures *o == 0` answers a later load of `o` by read-over-write, and
`ensures result == old(*o)` makes the result the load the caller already has
facts about. Neither needs an equation that a proof must find.

- **The stored value comes from the contract's text**, never from facts
  admitted after the call: only an `ensures` conjunct of the shape
  `place == expr` stores `expr`. Every other shape is an unknown store. This
  keeps the term fact-stable, and in `point-named-reads.md` it is a new
  coverage slice of `read_version`'s step 2.
- **`old(*o)` is evaluated through `read_version` at the call's entry point.**
  If the caller's memory holds a value for `*o`, that value is the result:
  in acceptance case 1, `p`, the non-null pointer the memory holds for `o`,
  not a fresh load.

## Acceptance cases

The Rust `Box` work paused on cases where loads and stores lose precision at a
call (`Option::take` as a library contract,
`fn take<T>(o: &mut Option<T>) -> Option<T> { owns *o; ensures result ==
old(*o); ensures *o == None; }`). The C forms below are regressions for this
design:

1. **Entry value of a result.**
   `int32* take(int32** o) { owns *o; ensures result == old(*o); ensures *o == 0; }`;
   `p = make(); *p = x; o = p; t = take(&o); if (t == 0) return 0; v = *t;
   release(t); return v;` with `ensures result == x`. The `t == 0` branch must
   be decided: `t` is the caller's load of `o`, which is `p`, which is not null.
2. **Exit value of a place.** `t = take(&o); if (o != 0) return 0; release(t);
   return x;` The branch on `o` must be decided: the call stored 0 to `o`.
3. **Framing a symbolic-size cell across a call.** Rust generic-stack `pop`:
   `let node = self.head.take()?; self.head = node.next; Some(node.value)`, with
   `Node<T>` laid out symbolically. The load of `node.value` (size `sizeof(T)`,
   offset `offsetof(Node<T>, value)`) must cross the `take` call, which owns
   only `self.head`. Today the call-havoc step gives up on any non-constant
   extent (`resource_tracker/step_effect.rs`, `CallHavoc`), and the node's
   two pointer loads are different `LoadedPointer` ids equal only by fact.
   Framing on cells with symbolic sizes, and one load per cell, are what fix
   it. It is also a regression for `point-named-reads.md` P2: framing a
   symbolic-size cell across a call is where the legacy walk stops.

A store that is recorded must be found by every later load of the same cell
however its address is spelled: an earlier attempt to replace the call's havoc
with the stated store was unsound because the havoc range and a later load
spelled the cell differently, so the load saw the pre-call value. Stores and
loads compare cells by the same identity.

## Abstract bytes

A complete foundation needs bytes that are richer than bit patterns, as
MiniRust's are: each byte is uninitialized, or a value with an optional
fragment of a pointer's provenance.

- **Uninitialized** bytes make `decode<T>` undefined. Click detects
  uninitialized reads today with special cases; they become a validity check.
- **Provenance fragments** let a pointer copied byte by byte (`memcpy`, a
  `char *` loop) keep its provenance, and make loading a pointer's bytes as an
  integer the provenance-dropping case that C (TS 6010) and Rust (exposed
  provenance) both define.

This is the last stage. The earlier stages do not depend on it.

## Raising

A load raises from its derivation (`pointer-model.md`, "Raising is by
derivation"): `n->next`, `p[i]`, `at(point, place)`, `exact(place)`, or
`load<T>(address)` when no place names it. The type spelled is the decoding's.

- A value raises at the type it was decoded at.
- A pointer load nested in an address, such as the inner load of
  `n->next->next`, raises through its place: the field, static slot or
  parameter declaration names it. Any of them names the same load, because
  the type does not change it.
- A pointer load that no place names raises as `load<Pointer>(address)`, at
  Click's untyped pointer type. It names the same load whatever type the
  kernel decoded it at.
- An integer or float load that no place names raises as `load<T>(address)` at
  its format. Whether effective-type checking accepts that for every such cell
  is open question 1.

## Migration

Version selection stays with `point-named-reads.md` and its owner. Each step
is one PR, measured with the gate harnesses, the raise-lower audit and
`click audit legacy-walk`.

0. **Click's untyped `Pointer` type.** Add `ProgramType::Pointer` and the
   Surface type `Pointer`: `load<Pointer>(a)` reads any pointer cell,
   `byte_offset` displaces it, casts to and from it keep the value, and
   `*q`, `q[i]` and `q + k` on it are refused. Additive; it gives step 1 the
   spelling for a pointer load that no place names. The kernel's pointer
   types are a flat list (`Int32Pointer`, `UInt8PointerPointer`, ...) that
   exists to carry pointee types; it shrinks as operations take them over,
   so step 7 is spread across the migration rather than last.
1. **Pointer loads by version point, not type.** Drop the value type from
   `PointerLoadId`'s key and registry. In `indexed_typed_version`, a pointer
   load matches a pointer store of the same category, object or function, of
   any type; the program-point session reviews this change to its file.
2. **`Load` and `AddressBase::Load`.** Introduce the interned `Load` and use it
   as the pointer base, replacing `LoadedPointer(PointerLoadId)` and the
   registry. Function-pointer loads move from load variables to it.
   *Done.* `Load` (`src/kernel/primitives/load.rs`) carries its point and
   cell and is interned by `(point.read_key(), cell)`; `Load::at` and
   `Load::base` are the only constructors, held by
   `build_support/read_construction.rs`. The category, object or function, is
   no part of the load: it is the decoding's, the type of the `Pointer` term,
   and a store lookup for a typed value passes it
   (`pointer_read_over_write_decoded_value`); a lookup about the base as an
   address asks about the cell's bytes and accepts a store of either
   category. Function-pointer reads already took the load base in step 1: an
   instrumented run of both gate harnesses minted no `FunctionSymbolic` load
   variable and resolved none, so the three adapters that read one as a load
   (`logical_pointer_read_term`, the graph's read definitions, and its input
   read test) are removed; `FunctionSymbolic` remains for function-pointer
   binders.
   `Address::loaded_value_at` names a memory-named load at the caller's
   point, keeping its legacy selection and so its identity.
3. **Integer and float loads on `Load`**, in two PRs, with the program-point
   session, whose constructors and ratchet gate these terms. Neither overlaps
   that session's own read-identity changes (its P1 producer moves); the two
   are scheduled apart so that failures stay attributable.
   - **3a.** `MemoryLoad` becomes `Load` plus a kind, keeping the kind's
     signedness in the key. Neutral: both harnesses pass, and the
     mixed-name census and legacy-walk counts stay flat. In two parts:
     - **3a-i, the representation.** *Implemented; one difference open.*
       `MemoryLoad(point, cell, kind)`
       holds a `ReadPoint`, the producer's selected point, and a `LoadCell`,
       the producer's address with its `Load::at(point, address)`, both built
       only by `read_operands` inside `MachineTerm::read_named`
       (`src/kernel/primitives/load.rs`; the ratchet counts `MemoryLoad(..)`,
       `read_operands(..)` calls, `ReadPoint(..)` and `LoadCell { .. }`).
       Equality, hashing and ordering go by `(Load, kind)`: the `ReadPoint`
       compares equal to every other and the address is not compared. That
       is the equivalence the term had, `(point, address, kind)`, within one
       memory arena: `ProgramPoint` equality is read-key equality there
       (legacy points compare their interned memory, whose id is the
       `ReadKey::Memory` key). Across arenas it is not: a legacy point
       compares two arenas' memories by content, while a `Load` keys them by
       arena id, so two memory-named reads of structurally equal memories in
       two arenas were one term and are now two, as pointer loads have been
       since step 2. That is intended: a new arena starts only with a new
       verification session, which also clears the load interner and every
       registry, so terms of two arenas never meet in one proof, and
       interning by memory content would hash structure on the hot path.
       The unit test
       `transported_equal_equation_from_a_new_epoch_drops_producer_source_events`
       (`src/kernel/eval/memory_loads.rs`) expects the two terms. An
       instrumented run of both gate harnesses
       compared the old and new equality on every comparison of two reads
       (over two million) and found no difference; both harnesses pass
       unchanged, and no session interned more than 10,000 loads. Ordering
       is by content, never by load id, since proof search iterates
       term-keyed sets in it and an id is a probe slot that depends on what
       the session interned before: a load orders by the hash of its point
       (as `ProgramPoint` hashes, by memory content for a legacy point) and
       cell, then on a tie by point and cell. The id's slot hashes the same
       content, not the read key, whose legacy form holds the arena token, so
       ids and term hashes do not vary with how many sessions ran before
       (`integer_reads_order_and_hash_the_same_whatever_was_interned_before`).
       A `cfg(test)` assertion in `Load::at` checks that a legacy point's
       memory belongs to the current arena, so the gate checks that terms of
       two arenas never meet; tests that probe the boundary on purpose say so
       with `allow_cross_arena_loads`. Consumers still read the selection from the
       term's `ReadPoint`, never from `Load::point`, which is the first
       selection of its key; a substitution or rewrite that changes the
       address rebuilds the read and so interns the new cell's load. Reads of
       one cell at two kinds share the load and stay two terms. Code that
       compared one field of two reads now says which:
       `point.point() == other.point()` or `cell.address() == other.address()`
       (26 sites, found by type-checking with the fields' comparisons removed;
       a direct `ReadPoint` comparison is always true).
       Term equality and hashing no longer walk the address
       (`src/scaling_tests/kernel/primitives/machine_integer/tests.rs`: a
       read's hash reads the same bytes at address sizes 4, 64 and 512 while
       the address's own hash grows; building a read costs the same with 16,
       256 or 4,096 others interned; 4, 64 or 512 reads of one cell at
       alternating selections and four kinds intern one load). Building a read
       now hashes its address once to intern the load, linear in the term
       built.
     - **3a-ii, the consumers** (program-point session). Consumers that
       branch on the selection (`is_entry_read`, `is_exact_read` with
       `has_certified_read_view`, `indexed_write`, the raiser) move to the
       load's key.
   - **3b.** One load per cell, decoded at each format; `Bits64` stops being
     special. The held-value and indexed lookups answer a load at another
     format of the same width, `decode<U>(encode<T>(v))`, where today they
     miss and fall to the legacy walk. This changes how terms print, so it is
     classified on its own. Signedness belongs to the decoding (decision 1),
     so no untyped `BitsN` kind remains. In four PRs:
     - **PR 1, pointer-word detours.** *Done.* Of the 41 production
       `LoadKind::Bits64` spellings, five built an eight-byte integer read
       only to name, compare or key a pointer load. The fact keys
       (`proof/fact_keys.rs`) key a pointer load by its load: its read key
       and cell, not shared with the eight-byte read of its cell (unit test
       `pointer_loads_are_keyed_by_their_load_and_not_by_an_integer_read`).
       The other four cannot become `Load`-based without changing what they
       decide, so they go through one bridge,
       `legacy_pointer_word_read(memory, cell)` (`primitives/load.rs`),
       building the same terms as before:
       `Address::canonical_read` and `canonical_loaded_value` select a pointer
       cell's version through `canonical_scalar_read`, whose identity cache,
       read observations and access widths are keyed by
       `(memory, address, kind)` and shared with 64-bit integer reads of the
       cell; and `pointers_equal_with_load_atoms` compares two load bases
       through its caller's load-atom rule, whose fact-dependent forms
       (`memory_loads_proven_equal`, `load_atoms_equal_modulo_origin_unchanged`,
       the quantified frame's `loads_unchanged`) decide frame equality of
       integer reads through `memory_history`. Replacing the bridge needs
       that selection and those frame checks keyed by cell and width; the
       program-point session owns the selection. The e-graph does not relate
       pointer loads through `Bits64` atoms: its pointer read definitions
       (`logical_pointer_read_term`) and several pointer-cell producers
       (`Address::version_read_value`'s fallback, `symbolic_pointer_load`,
       `symbolic_storage_cell_value`) build `Int32` reads of a pointer cell
       instead, a detour of the same kind that this PR leaves.
       `build_support/read_construction.rs` holds the bridge's callers (two
       each in `assumptions.rs` and `term_operations.rs`) and every
       production `LoadKind::Bits64` spelling, per file, at 37.
     - **PR 2, the algebraic stand-in.** *Done.* An algebraic read
       (`AlgebraicTermNode::MemoryLoad`) reaches walkers and load-atom
       comparisons through a stand-in, `memory_load_carrier`. It was an
       eight-byte integer read, `Bits64`, or `Abstract(T)` for a type known
       only by name; it is now the cell decoded at its own type,
       `LoadKind::Algebraic(T)`, which generalises `Abstract(T)` to every
       algebraic type (`LoadKind::of_algebraic`). Its identity stays
       `(Load, decoding)`: the stand-ins of one cell at two types, and the
       cell's integer read, share the load and are three terms (unit test
       `an_algebraic_read_is_its_load_decoded_at_its_algebraic_type`). Width
       and extent are unchanged: the model's eight bytes, or `sizeof(T)` for
       a type of abstract size (`LoadKind::extent`, `load_access_extent`).
       Version selection is untouched: the stand-in names the point and
       cell the algebraic read names. Each consumer that matched `Bits64`
       or `Abstract` for a stand-in now matches `Algebraic`: resolution
       against the cells (`resolve_memory_load_value`) returns the same
       decoding at the state's own point, the comparison form's algebraic
       read-over-write keeps excluding types of abstract size, and the
       native and retained havoc-framing collectors follow registered
       origins at the read's decoding. The value-level walkers
       (substitution, rewriting, variable collection) still take the
       stand-in through a `ProgramValue::UInt64` transport
       (`memory_load_carrier_value`): the tag only routes them to their
       machine-term arm, and unwrapping it would change their per-level
       work accounting. Type interning, now on this path, looks a
       structural type up among its name's candidates rather than scanning
       every interned type
       (`structural_type_lookup_and_algebraic_stand_in_do_not_scan_registered_types`).
       Spellings that change: a trace prints a stand-in as `read<T>`, not
       `read<Bits64>`, and a diagnostic describes one as "a value of an
       algebraic type", not "an eight-byte word". Surface raising still
       spells an unnamed stand-in as an `int64` load, as before; a
       `load<T>` spelling belongs with open question 1. The production
       `LoadKind::Bits64` spellings drop from 37 to 34
       (`build_support/read_construction.rs`): none remains in
       `primitives.rs` or the retained fold collector, and one fewer in
       `eval/memory_loads.rs`.
     - **PR 3** adds the e-graph sign relation at 16 and 128 bits.
     - **PR 4** splits `Bits64` into `Int64` and `UInt64`. The remaining
       spellings are genuine 64-bit integer reads: their construction from a
       format (`memory_state.rs`, `program_point.rs`,
       `cached_symbolic_storage_cell_value`), the wide-read observations and
       load variables (`eval/memory_loads.rs`, `read_observations.rs`), the
       wide-read value checks (`memory_history.rs`, `assumptions.rs`), the
       `UInt64` graph's read atoms (`equality_graph.rs`,
       `equality_graph/terms.rs`), and raising and diagnostics
       (`surface/`). The pointer-word bridge needs its cell-keyed
       replacement (PR 1) first, since neither signed nor unsigned is the
       decoding of a pointer's bytes.
4. **Algebraic and abstract loads** become decodings of `Load`. Step 3b
   PR 2 gives their stand-in the decoding, `LoadKind::Algebraic(T)`; the
   algebraic term itself (`AlgebraicTermNode::MemoryLoad`) still holds a
   point and an address, not a `Load`.
5. **Abstract bytes**: uninitialized bytes and provenance fragments.
6. **`loaded_value`** and the remaining scalar load variables go with the
   legacy walk.
7. **Untyped `Pointer`.** Once loads and stores state their own types, remove
   `program_type` from `Pointer` and `KernelPointer`. Today about 250 sites
   read it; all have an operation or declaration in reach except untyped
   `Load`/`Index` on an embedded value (lowering emits typed loads and byte
   offsets instead), store records and memory cells (they record their encode
   type), raising of stored pointers (raised by derivation or
   `load<Pointer>`), and `free`'s element width (from the allocation record).

## Design check

```text
Design check
- Part: Memory and checking (fast). No search is added.
- Why this part: every load is named, compared and answered here.
- Fast: a load's identity is an interned (point, cell): equality and hashing
  are O(1), as the side-table id is today. Store lookup reads the same
  point-index cell, keyed by the load's address, with a match on store
  category instead of type. Decoding is a per-type function of one load.
  Scaling: the existing load-identity and point-index scaling tests, plus
  one that grows the number of differently typed decodings of one cell and
  checks that they share one `Load`.
- Fact-stable: lowering names a load from its version point and cell; the
  type moves to the decoding lowering already builds. No fact is read.
- Failure: a load that no place names and that effective-type checking
  refuses at its own format does not raise; the raise-lower audit reports it.
```

## Decisions

1. **Signedness belongs to the decoding** (maintainer, 2026-11-23). Every
   integer width is one load per cell, decoded at each format, as `Bits64` is
   today. The `int8` and `uint8` values of one byte stay two terms, neither a
   conversion of the other (2026-10-30), as two decodings of one load related
   by the sign cast. A store at one format then answers a load at another of
   the same width, which no special rule has to add after the legacy walk is
   deleted.
2. **Pointer terms are untyped** (maintainer, 2026-11-23). Types live on
   operations and declarations (`pointer-model.md`, "Types belong to terms,
   not values"); Click's Surface type for an untyped pointer is `Pointer`.
   Whether a pointer designates an object or a function is part of its value,
   from its address base and provenance, not a type.
3. **Integer generality comes later.** Integer reasoning is partly generic
   over `MachineIntegerType` and partly written per format (a value variant per
   format; about 430 kernel functions named for one format, half of them for
   `int32`). Making it generic over the format is a separate design, after
   this one's integer steps.

## Open questions

1. **Effective type of an unnamed cell.** A specification `load<Pointer>`
   carries no pointee type, so effective-type checking must accept it for any
   pointer cell. An integer or float `load<T>` that no place names raises at
   its own format; check that effective-type checking accepts it for every
   such cell. A refusal leaves that load with no spelling, and is the defect
   to fix.
2. **Exactness.** *Resolved in step 2:* a load's identity is its read key
   and cell, so an `Exact` and an indexed selection of one point are one
   `Load`, as integer reads compare only `read_key()`. The load keeps the
   selection it was first built from, but nothing depends on which: a store
   lookup asks the index at the load's version point whatever the selection
   kind, and raising spells a read plainly where the place's ordinary read is
   that read key, `exact(..)` only where it is not
   (`mdtests/an_exact_and_an_ordinary_read_of_one_pointer_cell_are_one_load.md`).
   Integer load equality compares only `read_key()`, so an
   `Exact` and an `IndexedCell` selection of one point are one term; pointer
   loads match. Substitution and rewriting keep an exact load's point when
   they rewrite its address, and `exact-reads.md` E3 makes a pointer load's
   provenance the same kind of load as its address. `Pointer::from_read`
   names an exact load by the unchanged-bytes source, a memory-named key;
   where it coincides with a version-path load that is a mixed name, the
   pointer form of the 53 integer cases. The mixed-name census
   (`kernel::mixed_read_names`) extends to pointer loads once step 2 gives
   them one constructor.
3. **Interning cost** of `Load`. *Resolved in step 2:* interning is one hash
   probe on `(read_key, cell)`, charged one work unit only on a slot
   collision, equality and hashing compare one id, and ordering compares
   one stored content hash before falling back to structure on a tie
   (`src/scaling_tests/kernel/primitives/load.rs`): the work to intern a new
   load or find an interned one is the same with 16, 256 or 4,096 other loads
   interned; comparing two loads of a cell nested 4, 64 or 512 loads deep is
   the same; and 4, 64 or 512 reads of one cell, alternating exact and indexed
   selections and object- and function-pointer types, intern one load.
