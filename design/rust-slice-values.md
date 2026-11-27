# Rust slices as wide pointers

Status: direction agreed with the maintainer on 2026-11-25. Steps 0, 1,
2a, 2b-i, 2b-ii-a, 2b-ii-b, 2b-iii-a, 2b-iii-b-i and 2b-iii-b-ii of the
[plan](#plan) are done: the kernel has the wide pointer and its slice
pointer type, every kernel consumer reads or refuses its count, a slice is
stored and read back as one memory cell, a symbolic read of a slice cell
names its data pointer and count, a slice named by one variable, such as a
call's result or a binder, names its count from that variable, and a
slice-valued pure application names its count from the application, but no
front end produces a wide pointer yet.

## Requirements

Set by the maintainer on 2026-11-25. Every representation proposed here is
checked against all seven.

1. **First-class.** A slice is a core Rust construct and works well. It is
   not a special case that mostly works.
2. **Accurate in the kernel.** The kernel's representation means what a Rust
   slice means. There are no approximations or workarounds that hold only
   for the patterns tried so far.
3. **Unsafe-ready.** Unsafe Rust does not require an overhaul: building a
   slice from raw parts, taking its pointer, pointer arithmetic around it,
   and layout-level views.
4. **Full usage.** It covers `&[T]` and `&mut [T]`, and the patterns Rust
   code uses:
   - `len`, indexing, subslices `s[a..b]`;
   - `split_at` and `split_at_mut`;
   - iteration: `iter`, `iter_mut`, `enumerate`, `chunks`;
   - reborrows, and passing and returning slices;
   - slices in `Option` and in structs;
   - `&str` and `as_bytes`.
5. **Slicey everywhere.** Whatever the kernel holds raises to Rust slice
   syntax: `s`, `s.len()`, `s[i]`, `s[a..b]`. It never raises to tuples,
   matches or invented names.
6. **Complete in practice, including unsafe Rust.** Any true statement
   about a realistic program is provable. Nothing a program can observe
   about a slice is hidden from the logic:
   - its data pointer and that pointer's provenance;
   - its length and the address arithmetic between the two;
   - its relation to the memory it designates;
   - under unsafe code, its layout as raw words.
7. **Full equality.** Equality of slices is substitutive, so the e-graph
   may replace equals by equals in any context:
   - two slices are equal exactly when their pointers, provenance included,
     and their lengths are equal;
   - every operation built from a slice respects equality: its pointer, its
     length, indexing, subslicing and the range it designates;
   - every slice `s` equals the slice built from `s.as_ptr()` and `s.len()`.

## Decision

A Rust slice is a **wide pointer**: a kernel pointer with one more
component, its metadata, which for a slice is the element count. This is
Rust's own definition of every pointer to `[T]` or `str`.

### What a Rust slice is

Rust defines `&[T]`, `&mut [T]`, `*const [T]`, `*mut [T]`, `Box<[T]>` and
`&str` as **wide pointers**: a pointer to an unsized type is a thin data
pointer plus *metadata*, which for `[T]` and `str` is the element count
(Rust Reference, "Dynamically sized types"; `core::ptr::Pointee`,
`ptr::metadata`, `ptr::slice_from_raw_parts`). MiniRust, the reference
operational semantics, writes it the same way:
`Pointer { thin_pointer, metadata: Option<PointerMeta> }`, with
`PointerMeta::ElementCount` for slices and `VTablePointer` for `dyn`.
`&` and `&mut` are the same value with different types and aliasing
rules. `ptr::eq` on wide pointers compares address and metadata. Raw
slice pointers need no validity: `slice_from_raw_parts(p, n)` is safe to
build and unsafe only to dereference. The layout of the two words is not
guaranteed by Rust; rustc stores the data pointer first and the length
second.

### One value form, distinguished by type

`&[T]`, `&mut [T]`, `*const [T]`, `*mut [T]`, `Box<[T]>` and `&str` are one
kernel value form with six types. This is the choice Click already makes
for thin pointers: `&T`, `&mut T` and `*const T` are one pointer value
whose type decides what is owed and held, and pointer equality ignores the
type, so a cast keeps the value. Separate kernel forms would need a
conversion at every cast and reborrow, the boundary problem the hybrid
has. The type decides:

| Type | Entry facts | Authority | Other |
|---|---|---|---|
| `&[T]` | span, coverage of `s[0..s.len()]` | `views` | |
| `&mut [T]` | same | `owns` | |
| `*const [T]`, `*mut [T]` | none | none until dereferenced | |
| `Box<[T]>` | same as `&mut [T]` | `owns` | owns the allocation |
| `&str` | same as `&[u8]` | `views` | bytes assumed UTF-8 |

`Slice<T>` stays the spec name of `&[T]` and `Str` the name of `&str`;
specs may also write the Rust type. The other four are spelled as in Rust.

### Representation

- **Components.** `s.as_ptr()` is the thin pointer: the same address,
  provenance and array object, with no metadata. `s.len()` is the
  metadata. Both are components of the value, so they reduce on any
  pointer, opaque or constructed, with no unfold and no case split.
- **Equality.** Pointer identity adds the metadata. `add_pointer_equality`
  merges it with the other components. `s == t` holds exactly when
  address, provenance, array object and length are equal, and the e-graph
  substitutes either component. `ptr::eq` lowers to address and metadata
  equality, without provenance, as Rust defines it.
- **Opaque slices.** A parameter `s` is one value whose thin part is the
  parameter's pointer binding and whose metadata is today's
  `SliceLength` binding: the pair becomes the components of one value
  rather than two values. A call's result, a load and a pure function's
  result get their metadata the way they get their address: a named
  result, a load term, or a pure-application component, each with a
  Surface form (`w.len()`, `f(x).len()`).
- **Construction.** `s[a..b]`, `split_at`, `chunks` items and
  `slice::from_raw_parts(p, n)` build a wide pointer from a thin pointer
  and a count. A subslice owes `a <= b <= s.len()` where it is built and
  is recorded (`spec::required_constructions`) so it prints as `s[a..b]`.
  `foo[1..6].len()` is the component `5u64` and prints so.
- **Memory.** A wide pointer is stored and loaded as one pointer value of
  twice the word size, keeping provenance, as a thin pointer does. A
  program that reads the stored words as integers relies on rustc's
  layout; a target layout fact (data word, then length word) covers it
  when a program needs it.
- **Authority.** Unchanged in kind: `views *s` is the range
  `s.as_ptr()[0..s.len()]`. Indexing reads at the thin pointer plus `i`
  with Rust's bound check `i < s.len()`.
- **The library.** `spec enum Slice<T>` in `library/rust/slice.click` is
  removed. `Slice<T>` names the built-in type; `slice::len`,
  `slice::as_ptr` and `slice::from_raw_parts` are its two components and
  its constructor. `slice::subslice_len` is no longer needed.

### Risks to settle first

1. **Consumers of a pointer that assume it is thin.** Arithmetic,
   dereference, range formation and integer casts must take the thin part
   or refuse a wide pointer. There are 203 `Pointer::new` sites in 72
   files outside tests. The type distinguishes wide pointers, so a
   consumer that does not handle one refuses it rather than misreading it.
   The inventory is [below](#inventory-of-pointer-consumers).
2. **Pointer fields under constructor injectivity.** `Some(s) == Some(t)`
   must give `s == t` componentwise. This was a gap for thin pointers too,
   fixed in step 0; the length joins the same rule.
3. **Scaling.** Metadata is one more component per pointer node and one
   more pair per pointer equality.

### Inventory of pointer consumers

Taken 2026-11-25 from `master`. Core sites were read;
the rest were classified by function name and grep counts, so per-site
behaviour in the large evaluation files (`eval/memory_loads.rs`,
`eval/expression.rs`, `kernel/spec.rs`, `surface/proof/surface_synthesis.rs`)
is still to be confirmed.

**Choke points.** `Pointer` is the written view of the kernel payload
`KernelPointer`, whose fields only `kernel_term/pointers.rs` and its
`written.rs` reach, so metadata flows through a few places:

- `Pointer::identity()` (`kernel_term/pointers/written.rs`) for equality, hash and order,
  plus `same_provenance_as` and `retained_nonaddress_metadata`;
- `map_pointers`, `try_map_pointers` and `map_addresses` (`:3256-3283`)
  for substitution and transport, which today map addresses only and need
  a parallel map over the length term; `pointers()` (`:3293`) for variable
  collection;
- **a second pointer form**, `KernelPointer`/`SharedPointer`
  (`kernel_term/pointers.rs:108-265`), with its own equality and
  `import`/`export`. Metadata must be carried there too or it is dropped
  at every kernel-term crossing.

The ~400 `ProgramValue::Pointer(` sites that move whole values need no
change.

**Sites that need handling (H)**, in order:

1. Identity and `SharedPointer` (above).
2. E-graph: interning (`congruence.rs:1340-1356`) puts a pointer's
   non-address parts into an opaque head; the length must be its own
   `Apply` operand so equal lengths are congruent, and
   `add_pointer_equality` (`:1687`, `equality_graph.rs:1668`) closes the
   length pair.
3. Pointer equality conditions: `pointer_equal`
   (`kernel_term/boolean/complete_pointer.rs:139-200`) and
   `OldConditionTerm::pointer_equal` (`term_operations.rs:3852`) gain a
   length conjunct, since Rust's `==` on raw slice pointers compares it.
4. Substitution and variable collection (the choke points above;
   `reasoning/variable_collection.rs`, 12 sites).
5. Fact keys (`proof/fact_keys/pointer_keys.rs`, `fact_keys.rs:2288`).
6. Memory: about 40 sites assume an 8-byte pointer cell
   (`ProgramType::byte_width`, `C_POINTER_BYTE_WIDTH`,
   `memory_history.rs:3055-3531`, the loaders in `memory_loads.rs`). A
   wide pointer is a 16-byte cell whose load rebuilds both words.
7. Certification (`retained_syntax/pointers.rs`) and printing
   (`rust_spelling.rs:65-119`, which today re-pairs two arguments into
   `slice::from_raw_parts(p, n)`, and `surface_synthesis.rs`).

**Sites that must refuse a wide pointer (R):** pointer arithmetic
(`operators.rs` `pointer_offset_by_elements_paths`,
`pointer_offset_by_bytes_paths`; spec `PointerOffset`,
`PointerOffsetBytes`), subtraction and pointer difference, ordering,
bitwise tag operations, pointer-to-integer and integer-to-pointer casts
(`expression.rs:980-1129`), and the retyping builders `with_type`,
`retag_pointer` and `with_binding_type` (thin to wide must carry a length).
The type alone does not refuse them: `is_pointer` derives from
`pointee_type()`, but the operators take their step width from the
expression, not the value's type, and default to 4 without one, so a
slice would be stepped as an `int *`. Step 2b-i therefore refuses a wide
operand explicitly at each operator's entry (`RuntimeError::
ThinPointerRequired`), and the ~100 `PointerInteger` sites are only
reachable after a cast that refuses.

**Sites that take the thin part (T):** ranges, resources, aliases,
mutexes and borrows match on `AddressBase` only; the range base at
`contract_certification.rs:1624`; most of the ~70 construction callers,
which build thin pointers.

**`ProgramType`** is a `Copy` enum with 29 pointer variants.
`PointerArray(PointerArrayElement, u32)` is the pattern for a
`SlicePointer(element, kind)` variant that stays `Copy`. About 20 files
match `Float64PointerPointer` by name; which of them are exhaustive is to
be checked when the variant is added.

**Today's pair.** Parameters: `rust/lowering.rs:975-1023` (pointer
parameter with `slice_length_parameter`, plus a `UInt64`
`BindingName::slice_length`); locals: `local_slice_length`
(`lowering.rs:1446-1457`, `memory_state.rs:1378`), written together at
`:1813-1838` and read by `slice_parts`/`indexed_parts`; entry facts at
`contract_certification.rs:1634-1670`. These become the two components of
one value.

## Usage patterns

| Rust | Kernel | What it proves | Prints as |
|---|---|---|---|
| `fn f(s: &[u8])` | one wide pointer: parameter pointer + `SliceLength` binding | entry: span and coverage of `s[0..s.len()]` | `s` |
| `fn f(s: &mut [u8])` | same, `&mut [u8]` type | entry `owns *s` | `s` |
| `s.len()` | metadata component | equals the count it was built with | `s.len()` |
| `s[i]` | read at thin part `+ i` | owes `i < s.len()` and a covering resource | `s[i]` |
| `s[a..b]`, `&mut s[a..b]` | construction: thin `+ a`, count `b - a` | owes `a <= b <= s.len()`; lends the subrange | `s[a..b]` |
| `s.split_at(k)`, `split_at_mut` | two constructions | owes `k <= s.len()`; `_mut` lends disjoint `owns` | `s[..k]`, `s[k..]` |
| `s.iter()`, `iter_mut`, `enumerate` | iterator over the thin range | item `k` is `&s[k]` | `s[k]` |
| `s.chunks(n)`, `chunks_exact` | item `k` a construction | item `k == s[k*n..k*n+n]` | `s[k*n..k*n + n]` |
| `&*s`, `&mut *s` (reborrow) | the same value | a new loan of the same range | `s` |
| `g(s)`, `return s` | one argument, one result | callee facts about `result.len()` reach the caller's `w.len()` by substitution | `w`, `w.len()` |
| `Option<&[u8]>` | `Option` over a wide pointer field | `Some(s) == Some(t)` gives `s == t` (after item 2) | `Some(s)` |
| struct field `&'a [u8]` | a pointer cell of twice the word size | load returns the stored value with provenance | `x.field` |
| `&str`, `s.as_bytes()` | wide pointer typed `&str`; `as_bytes` retypes | UTF-8 of the range is assumed | `s`, `s.as_bytes()` |
| `slice::from_raw_parts(p, n)` | construction | caller owes validity: coverage, span, alignment | `slice::from_raw_parts(p, n)` |
| `s.as_ptr()`, `s as *const [T]` | thin component; retyping | same address and provenance | `s.as_ptr()` |
| `ptr::slice_from_raw_parts(p, n)` | construction, no validity owed | none until dereferenced | `ptr::slice_from_raw_parts(p, n)` |
| `ptr::eq(s, t)` | address and metadata comparison | Rust's `ptr::eq` | `ptr::eq(s, t)` |

## Alternatives considered

### Kernel facts the options rely on

- `Pointer` (`src/kernel/primitives/kernel_term/pointers/written.rs`) is already a compound: an
  address, its provenance and its array object. Its identity, hash and
  order use those components, not its type.
- The e-graph decomposes pointer equality by component:
  `add_pointer_equality` (`equality_graph/terms/congruence.rs:1687`)
  merges provenance, bounds and the address separately, and a pointer
  argument is interned as an application over those components
  (`congruence.rs:1340`). So pointer equality is already full and
  substitutive, provenance included.
- Constructor injectivity (`join_constructor_applications`,
  `terms.rs:2485`) merged whole field nodes, and no rule split a merged
  pointer field back into its components, so `Some(p) == Some(q)` did not
  give `address(p) == address(q)`. This affected every option that puts a
  slice, or any pointer, inside `Option`; step 0 fixed it for all pointer
  values.
- There is no eta (surjective pairing) rule: `s == Slice(as_ptr(s),
  len(s))` is not built in, and `slice::len`/`slice::as_ptr` are opaque
  `match` functions until unfolded. A `match` is an opaque atom with no
  congruence on its scrutinee, and its binders are counter-numbered.
- A slice parameter is already two kernel bindings: the parameter's
  pointer and a `BindingName::SliceLength`, stored at
  `AddressBase::SliceLength`. Entry adds the span fact
  (`len * width <= isize::MAX`) and coverage of `p[0..len)` within one
  object (`contract_certification.rs:1634`). There is no non-null or
  alignment fact.
- Memory cells hold `ProgramValue`s. A pointer stored in memory and loaded
  back keeps its provenance. No algebraic (spec enum) value is stored in
  memory today; `ProgramValue::Parameter` carries only an abstract type
  parameter's value.

### Options and how they fare

- **A. Today's hybrid.** Pointer and length pairs for parameters and
  importer locals; `spec enum Slice<T>` for pure-function results,
  `Option` payloads and enum fields; conversion where they meet.
- **B. `Slice<T>` everywhere,** with a kernel projection for a one-variant
  enum (the proposal this note made before the requirements, which this note
  replaces).
- **C. A built-in product value** with `data` and `len` projections (the
  [2175760b9 proposal](https://github.com/clicklang/click/blob/2175760b9/design/first-class-slices.md),
  not adopted then because the fold and `peel` machinery only worked on
  pairs; the hybrid was the cheaper path to working proofs).
- **D. A wide pointer:** `Pointer` gains an optional metadata component,
  the element count, and a slice is a pointer value whose type is a slice
  pointer type (`&[T]`, `&mut [T]`, `*const [T]`, `*mut [T]`, `&str`).

| Requirement | A. Hybrid | B. `Slice<T>` everywhere | C. Built-in product | D. Wide pointer |
|---|---|---|---|---|
| 1. First-class | Fails: two representations, conversion at every boundary | Meets in specs; a datatype wrapping a pointer | Meets | Meets: the language's own form |
| 2. Accurate | Fails: a slice is two variables in one place, an enum in another | Partly: a slice is not a datatype in Rust; `*const [T]` and `&[T]` differ only in type there, but here one would be an enum and `*const T` a pointer | Meets for `&[T]`; raw slice pointers become a second form or casts change category | Meets: same shape as Rust and MiniRust for all six types |
| 3. Unsafe-ready | Fails | Fails: a slice stored in a struct or `Vec` in memory needs algebraic values in memory cells, a new memory-value kind; `as *const [T]`/`as *const T` casts change representation | Partly: needs its own memory cell kind and layout; `&dyn` later needs another product | Meets: memory already stores pointers; casts are retyping or projection; `dyn` adds a metadata kind, not a new value form |
| 4. Full usage | Fails: no locals, returns or `Option` in program code without per-site flattening | Meets after the memory-value work | Meets after the memory-value work | Meets; `&`/`&mut` are types, as for thin references |
| 5. Slicey | Partly: case-split names (`field_slice_1`) leak | Needs printing for projections and for the constructor of a parameter's fields as the bare `s` | Same as B | Prints as a pointer prints: the binding `s`, `s.len()`, `s.as_ptr()`, `s[a..b]` for a recorded construction |
| 6. Complete in practice | Fails: facts stated over `slice::len(r)` and over a field read of `r` never meet | Needs eta and pointer-field splitting, both new | Needs eta and injectivity, both new | Pointer components already carry provenance and bounds; metadata is one more component |
| 7. Full equality | Fails: no eta; pair and value are different terms | Needs an eta rule for one-variant enums and pointer splitting under injectivity | Needs both, built for a new value | Already componentwise for pointers; eta holds by construction because `s.len()` and `s.as_ptr()` *are* components of `s`, not functions of it |

A's failure is already observed. An unmerged prototype of slice returns
on A got three of four fixture functions working; the fourth
(`first_byte`) failed on `0u64 < field_slice_1`, a fact about a case-split
name that the callee's contract, stated over `slice::len(r)`, never
reaches.

B and C can be brought to meet every requirement, but each needs three
new mechanisms that D gets from the pointer it already is: substitutive
componentwise equality, eta, and storage in memory with provenance. B and C
also leave raw slice pointers and `dyn` pointers as further forms to add.

## Design check

```text
Design check
- Part: Kernel values and equality (Pointer metadata, identity, e-graph
  interning) — fast; Symbolic execution (component reads, construction,
  memory cells of a wide pointer) — fast; Frontends (Rust lowering, sidecar
  parser) — fast; Resources (ranges over the thin part) — fast.
- Why this part: every proof that touches a slice reads its pointer and
  length on every step, so the read must be the simple checked operation
  it is today, not a search.
- Fast: a component read takes the value from its operand, O(1); it reads
  no fact, path, state or resource collection. Construction builds one
  Pointer from a thin pointer and a count. Pointer equality merges one more
  component pair. Range authority keys the existing resource index by the
  thin pointer, as today. Scaling tests (src/scaling_tests/kernel/, new):
  component reads of a slice parameter at 8/32/128 unrelated facts and
  8/32/128 unrelated slices stay flat in deterministic work; equalities
  among 8/32/128 wide pointers grow linearly in e-graph work; a function
  with 8/32/128 slice locals passed through calls grows linearly.
- Slow: no slow-part reasoning is added. close() sees components as
  ordinary terms.
- Fact-stable: lowering reads no facts to build a slice's term. A
  component of a constructed slice is its own component, a property of the
  term, not of facts. Run scripts/audit.sh fact-stability before and after.
- Raise-lower: a wide pointer raises as its binding (`s`, `w`), its
  components as `s.as_ptr()` and `s.len()`, a recorded construction as
  `s[a..b]`, any other construction as `slice::from_raw_parts(p, n)`. Each
  lowers back to the same term. No case-split names appear.
- Failure: an operation given a wide pointer where it needs a thin one
  refuses, naming the operation and `.as_ptr()`; a slice index keeps "Rust
  slice index panic check: could not show i < s.len()".
```

## What changes

The front-end and test inventory is from 2026-11-25 (`master` plus an
unmerged slice-return prototype). The kernel inventory is
[above](#inventory-of-pointer-consumers).

- **Rust front end:** about 100 sites in 12 files, `src/languages/rust/`:
  - parameter lowering (`lowering.rs`, `ByteSlice`/`ScalarSlice` arms);
  - slice locals (`declare_slice_length`, the `slices` and
    `shared_scalar_slices` maps, `moves.rs` declarations);
  - `slice_parts` and `indexed_parts` (about 20 callers);
  - call argument spreading;
  - `split_at` (`slice_split_slots`);
  - slice iterators, chunks and enumerate (`lowering/{shared_arrays,chunks,enumerate}.rs`
    and their `charon/` counterparts);
  - borrow frontiers;
  - about 13 `charon/temporaries.rs` folds that special-case slice
    temporaries or `SliceLength`.

  Iterators keep their own fields (remaining pointer and length); only
  their construction from a slice and their yielded slices change.
- **Surface:**
  - `FunctionParameter::rust_slice_length` and the about 20 constructors
    that set `slice_length`;
  - `take_rust_slice_len`, `rust_slice_params` and `rust_slice_locals`;
  - `spread_slice_arguments` for pure-function calls, which goes away;
  - derived authority in `parser/rust_reference_authority.rs`;
  - `slice_method` in `validation/constructor_inference.rs`;
  - printing in `diagnostics/rust_spelling.rs`, which matches pointer and
    length pairs back to a slice today and prints the value directly
    after the change.
- **Kernel:**
  - `Pointer` gains the metadata component; identity, hash and order
    include it; `ProgramType` gains slice pointer types;
  - e-graph interning and `add_pointer_equality`; substitution and
    transport of pointer values;
  - memory cells of a wide pointer;
  - the entry facts (`contract_certification.rs`) stated over the
    parameter's components, chosen by type;
  - `ProgramParameter.slice_length_parameter` and
    `AddressBase::SliceLength` become the metadata of a parameter or local,
    not a second value.
- **Library:** `spec enum Slice<T>` removed; `Slice<T>`, `slice::len`,
  `slice::as_ptr` and `slice::from_raw_parts` name the built-in type and
  its operations; `str.interface.click` states `as_bytes` as
  `result == s` retyped.
- **C and C++:** no behavior change. A thin pointer has no metadata.
- **Tests:**
  - 161 of 473 Rust import tests mention slices;
  - 44 `design/charon-trial/` fixtures, 12 `examples/rust-*` projects,
    3 `tests/fixtures/rust-verification/` entries and a few mdtests;
  - Rust scaling tests under `src/scaling_tests/languages/rust/`.

  Proofs that read `b.len()`, `b[i]` and `*b` keep their text. Proofs that
  print or compare a slice parameter's pointer as `b` change to
  `b.as_ptr()`.

## Source compatibility

A Rust sidecar writes `b.len()`, `b[i]`, subslices and `views
b[0..b.len()]` as today. One spelling changes meaning. A bare `b` naming a
slice parameter is now the slice, as in Rust, not its data pointer. So
`ensures result.as_ptr() == b` becomes `ensures result.as_ptr() ==
b.as_ptr()`, or `ensures result == b`. The migration makes every sidecar in
the repository that compares a slice's pointer write `.as_ptr()`. A sidecar
that writes the old form gets a type error naming `.as_ptr()`, never a
silent change of meaning.

## Plan

Each step lands green. No step keeps two representations of the same
construct.

0. **Pointer fields under injectivity.** Done. `Some(p) == Some(q)` did
   not give `p == q` componentwise for thin pointers either. A class merge
   of two complete pointer values now joins their provenance, bounds and
   addresses, as a stated pointer equality does
   (`constructor_injectivity_splits_pointer_fields`).
1. **Inventory** of every `Pointer` consumer, classified as takes the thin
   part, refuses a wide pointer, or handles metadata. Done; recorded
   [above](#inventory-of-pointer-consumers).
2. **Kernel wide pointer**, in two parts.
   - **2a. Metadata component.** Done. `KernelPointer.metadata` is
     `Option<Arc<KernelPointerMetadata>>`, whose one kind is
     `ElementCount` (a `UInt64` term; a `dyn` vtable would be a second
     kind). `Pointer::with_element_count`/`SharedPointer::with_element_count`
     build one from a thin pointer and a count; `as_ptr` and `len` read the
     components in place. Identity (`written.rs`), storage keys and fact
     keys add the count after the thin identity and hash nothing for a thin
     pointer, so thin hash streams, order and equality are unchanged.
     `map_pointers`/`try_map_pointers` take a count map, the kernel rewrite
     maps it as a numeric child, and variable, load, read and memory
     collectors visit it (`Pointer::metadata_terms`). The e-graph interns
     the count as one more `Apply` operand, and `add_pointer_equality`,
     `join_pointer_components` (constructor injectivity) and class merges
     join the count pair. `pointer_equal` keeps the complete `PointerEqual`
     for a wide operand instead of reducing to `AddressEqual`; deciders that
     reduce a complete equality to addresses (`pointer_offset_sides`,
     `decide`, the state-modulo condition matchers, pointer translation and
     the rewrite's graph check) require equal metadata first. Raising to
     Surface, diagnostics rendering, memory stores, allocation rebasing and
     frame transport refuse a wide pointer with an internal error naming
     step 2b (`Pointer::expect_thin`). Tests: `kernel_term::pointers`,
     `equality_graph::wide_pointer_tests` and
     `constructor_injectivity_splits_wide_pointer_counts`; scaling tests
     `wide_pointer_equality_chains_grow_linearly`,
     `wide_pointer_components_ignore_unrelated_facts` and
     `wide_pointer_component_reads_stay_flat`.
   - **2b. Types, cells and raising**, in three parts. Raising cannot
     land before the Surface type: a raised `s.len()` or
     `slice::from_raw_parts(p, n)` must lower back to the wide pointer,
     and today the Surface `Slice<T>` is the library's enum. Memory cells
     are their own subsystem, with their own scaling tests. So:
   - **2b-i. Slice pointer types and consumers.** Done.
     `ProgramType::SlicePointer(SliceElement)` is the type of every wide
     pointer and of no thin one: `with_element_count` widens `T *` to
     `[T]` (or `str`, by retyping), `as_ptr` narrows it back, and
     `Pointer::new` at a slice type, or a `with_type`/`with_binding_type`
     between a thin and a slice type, is an internal error. `&`/`&mut`,
     raw and `Box` slices are one kernel type, told apart by the
     declaration's qualifiers and contract as thin `&T`/`&mut T` are. It is
     16 bytes, 8-aligned, and has no pointee type. Arithmetic, ordering,
     equality, bitwise operations, member offsets and selections,
     dereferences (`Load`, `TypedLoad`, spec `MemoryLoad`), spec
     `PointerOffset`, coercions, truth tests and every cast that would add
     or drop a count refuse a wide operand with `ThinPointerRequired`,
     naming the operation and `.as_ptr()`; a cast between slice types keeps
     the count. `pointer_provenance_match`, which its address-comparing
     callers read as "equal in all but the address", now requires
     known-equal metadata (`pointer_metadata_known_equal`: the same count
     term or one `UInt64` class), so each of its callers is complete for
     wide pointers; the 2a guards beside `decide` and the condition
     matchers fold into it. `map_addresses` takes a count map: load
     canonicalization and the address-equality rewrite respell a count's
     reads as they respell the scalars beside it, rather than keeping it.
     Condition preparation registers a count's machine operands. Rebasing a
     pending allocation keeps a slice's count, as it keeps a bounds width.
     Diagnostic text (`describe_condition`, the proof renderer) prints a
     wide pointer as `slice::from_raw_parts(p, n)`. Tests: `kernel::tests::
     slice_pointer_tests`, `a_slice_equality_is_described_with_its_count`;
     scaling test `wide_pointer_value_matches_stay_flat`.
   - **2b-ii. Memory cells**, in two parts: the stored cell, then
     symbolic reads of it.
   - **2b-ii-a. Slice cells.** Done. A wide pointer is stored as one
     16-byte cell (`store_with_effective_type` no longer refuses it); a
     program store of one ends every cell it overlaps, and a store into
     either word ends it, as for any cell of its width. A program read of
     the cell at its own slice type returns the stored slice, count
     included. Every read that would take one word of the cell refuses
     with `LoadTypeMismatch` until a layout fact exists: a thin pointer,
     an integer, a byte, either word, or the cell at another slice type.
     The thin read-over-write paths close to a stored slice at their
     sources, so the load sites that retype a stored pointer
     (`stored.with_type(value_type)` in `memory_loads.rs`) and those that
     rebuild a read at the stored value's type (`logical_read_equation`,
     the stored-value equalities of `register_logical_read_values`,
     `comparison_form_uncached`) never receive one: no `LoadKind` reads a
     slice (`LoadKind::of_value`), no pointer decoding answers with one
     (`decodes_as`), and complete-pointer recovery
     (`complete_pointer_carrier_read_retained_value`) recovers none. A
     logical read of a slice cell names its version, as a pointer read
     does (`logical_read_names_its_version`); with no symbolic slice read
     yet, it refuses rather than lowering to the stored slice. Tests:
     `kernel::tests::slice_cell_tests`; scaling test
     `slice_cell_store_and_read_ignore_unrelated_cells`.
   - **2b-ii-b. Symbolic slice reads.** Done. A symbolic read of a
     slice cell (`symbolic_load_value_unrecorded`, and the slice branch of
     `canonicalized_retained_symbolic_load_value_with_identity`) is the
     slice its load decodes to, `Pointer::slice_read`: its data pointer is
     `AddressBase::SliceData(load)` and its count the read
     `MemoryLoad(point, cell, LoadKind::SliceCount)`, both named by the one
     `Load` of the cell. Neither is a thin pointer read (`AddressBase::Load`)
     or an integer read of either word, so no slice read equals a word read
     without a layout fact. The count is a `u64` read whose extent is the
     whole 16-byte cell. A logical read of a slice cell and a read of an
     unknown one name the read; the 2b-ii-a refusal is gone. Read-over-write
     is one authority, `stored_slice_of_load`: the store the load's version
     point indexes (`ProgramPoint::indexed_slice_version`), else the
     memoized version walk the pointer authority takes. The whole read
     (`slice_read_over_write_value`), its data pointer
     (`pointer_read_over_write_decoded_value`, so `stored_pointer_address`
     and the `AddressEqual` comparison form follow) and its count
     (`read_over_write_value`, through `LoadKind::read_cell`) resolve to the
     stored slice's; `comparison_form_uncached` resolves a slice side,
     including one whose count the scalar batch already replaced, and folds
     two equal slices. A read of a stored slice carries the read equation.
     `register_logical_read_values` joins a slice read with the stored
     slice, data pointer and count (`add_pointer_equality`). Frame transport
     carries a count as a numeric child
     (`transport_framed_atomic_bitvector`), as it carries the loads of an
     offset; a slice read's data pointer keeps its load, as a pointer read's
     base does. The opaque-block consumers that group `AddressBase::Load`
     (may-alias, symbolic-block, unresolved-pointer, carrier and resource-read
     sets) include `SliceData`. Raising a count refuses with an internal
     error until 2b-iii, as raising a wide pointer does. Tests:
     `kernel::tests::slice_cell_tests` (the 2b-ii-b cases),
     `memory_history::tests::framed_transport_carries_a_slice_count`;
     scaling tests `symbolic_slice_reads_ignore_unrelated_cells` and
     `unknown_slice_cell_reads_stay_flat_as_reads_grow`. Not done here: a
     cell that holds its own slice read (a materialization) reads as the
     stored slice through the read equation, not as that read; and the
     state-aware alpha key of a slice read's data pointer is its load's
     identity alone, so two reads at alpha-equivalent states key apart.
   - **2b-iii. Opaque slices, Surface type and raising**, in four parts.
     The Surface `Slice<T>` cannot become the built-in type while a slice
     the Surface already writes has no kernel value: a theorem's or pure
     function's slice parameter, a slice-valued pure function's result, a
     quantified or matched slice. And the enum cannot stay beside the
     built-in type, which would be two representations of one slice. So
     the kernel names every opaque slice's count first (2b-iii-a,
     2b-iii-b-i, 2b-iii-b-ii),
     then the Surface type replaces the enum in one step with its raising
     (2b-iii-c), then strings (2b-iii-d).
   - **2b-iii-a. Slices named by a variable.** Done. A slice named by one
     variable `v` has thin part `Address::symbolic(v)` and count
     `Variable(v.element_count())`: a `UInt64` variable whose identity is
     `v`'s plus the component, so one name gives both components with no
     second allocation, and the count raises from the slice's name
     (`Variable::counted_slice`). A count is no ordinary, bound, witness,
     match or produced variable (every origin predicate is false for it),
     orders after every variable that is not one, so
     `Variable::FIRST_NON_ORDINARY` still bounds the ordinary ones, and
     hashes as `v` plus one word, so every other variable hashes as before.
     `symbolic_call_result` builds such a slice for a slice type, in place
     of its internal error: a slice-returning call's result, an exception
     payload, a termination parameter and a case binder's payload. A count
     is an independent variable to the logic, so a pass that renames or
     closes over `v` alone leaves a valid fact about a fixed count; only the
     naming link is lost, which 2b-iii-b-i closes for binders. Raising a count
     refuses with an internal error until 2b-iii-c. Tests:
     `kernel::tests::slice_call_result_tests`; scaling test
     `a_named_slice_ignores_unrelated_slices_and_facts`.
   - **2b-iii-b. Slice binders and slice-valued pure applications**, in
     two parts: binders, whose count is already named (2b-iii-a), then
     pure applications, which need a count term of their own.
   - **2b-iii-b-i. Slice binders.** Done. A slice binder (a quantifier's
     sort, a choice witness, a `match` arm's payload) is a variable-named
     slice (`Sort::symbolic_pointer_value`, which refused a slice sort
     before), and closing, opening, renaming
     and substituting it carry `v` and `v.element_count()` together.
     `quantifiers::rename_slice_count` renames the count beside every
     rename of `v`: `rename_quantified_variable` (so `close_forall`,
     `close_exists`, `open_quantifier` and `canonical_binders`), choice
     opening in the proof object, and the alpha comparison and capture-free
     alignment of `contract_certification`, whose freshness and capture
     checks read a free count as naming its slice. The typed rewrite
     (`TermRewrite::for_typed_variables`, behind instantiation and `match`
     reduction) maps the count of a binder replaced by a slice value to the
     value's count and the count of a scope-renamed binder to the new
     binder's count, one lookup of the counted slice per count leaf; a
     replacement that mentions a count mentions its slice for capture. A
     substitution of `v` by a thin address
     (`substitute_pointer_variable_in_proposition`) leaves the count alone,
     a valid fact about a fixed count; the rewrite's whole-formal
     replacement of a slice keeps the thin type for the thin part and
     rewrites the count as a numeric child. Thin binders are unchanged. Theorem
     and pure-function parameters reach the kernel as quantifiers and
     lowering environments; no front end gives one a slice sort until
     2b-iii-c. Tests: `kernel::tests::slice_binder_tests`; scaling tests
     `closing_a_slice_binder_grows_linearly_with_unrelated_slices` and
     `instantiating_a_slice_binder_ignores_unrelated_binders`.
   - **2b-iii-b-ii. Slice-valued pure applications.** Done. Kernel only. A
     pure application of slice type (a branch of its own in `spec.rs` beside
     the pointer-result branch, `spec::pure_slice_application_value`) is a
     wide pointer whose thin part is based on
     `AddressBase::PureFunctionApplication(app)` at the element's thin
     pointer type and whose count is `OldMachineTerm::PureApplicationCount(app)`,
     `f(x).len()`: a `UInt64` term keyed by the application's identity,
     never an integer application of the same name. It follows every other
     `OldMachineTerm` variant, so their derived order is unchanged. In the
     e-graph the count is the `ArgumentTag::PointerCallCount` projection of
     the application's `PointerFunctionIdentity` node, beside the provenance
     and bounds projections `retain_pointer_call_component` makes, so the
     counts of applications to equal arguments are equal; one key lookup
     per count, the identity's definition queued once. The count is an
     exact scalar leaf of the `KernelTermNode::PointerCall` value's
     metadata. Frame transport keeps it, as it keeps the application block
     of the thin part. Every rewrite rewrites its application's arguments
     and names the count of the rewritten application: `TermRewrite::bits`
     argument by argument (never reading the application as an integer
     call, so no replacement of `f(x)` applies to it) and
     `substitute_bitvector_variable` through the application's call term;
     the variable, capture, binder and scope collectors read the
     application's arguments. A definitional unfolding, `f(x) == body` at
     slice type, lowers to the complete pointer equality, so
     `add_pointer_equality` joins both components with the body's slice.
     Raising the count refuses with an internal error naming 2b-iii-c; a
     diagnostic describes it as `f(<typed Click arguments>).len()`. No front
     end produces a slice-valued application until 2b-iii-c. Tests:
     `kernel::spec::slice_application_tests`,
     `kernel::equality_graph::slice_application_tests`,
     `framed_transport_carries_a_slice_application_count`,
     `raising_a_slice_application_count_refuses`; scaling tests
     `slice_application_counts_ignore_unrelated_applications` and
     `interning_application_counts_grows_linearly`. The equality-rewrite
     atom index (`bitvector_equality_atom_key`) files a count by its
     application's identity.
   - **2b-iii-c. Surface slice type and raising.** `spec enum Slice<T>`
     is removed in the same step as the built-in type arrives: `Slice<T>`
     lowers to `ProgramType::SlicePointer` and gets an interface type
     (`interface_type_from_program_type` panics today);
     `slice::from_raw_parts(p, n)`, `slice::len` and `slice::as_ptr` are
     name-table entries for the constructor and the two components, not
     functions with bodies; `s.len()`, `s.as_ptr()` and a recorded
     `s[a..b]` lower to the components and a construction, and
     `slice::subslice_len` and `Slice::Slice(p, n)` go. Raising replaces
     every refusal: the `expect_thin` sites in `surface_synthesis.rs` and
     `render/surface.rs`, `load_type_spelling` and the `SliceCount` read,
     `SliceData`-based pointers, element-count variables and pure-application
     counts, each lowering back to the same kernel term in the same
     context. `rust_spelling` prints a slice directly rather than pairing a
     pointer with a length. Slice-valued pure functions, `Option<&[u8]>`
     contract payloads and slice-returning functions use the kernel forms of
     2b-iii-a and 2b-iii-b. Rust slice parameters stay spread into a
     pointer and a length until step 3, so a sidecar's bare slice argument
     is the construction `slice::from_raw_parts(bytes, bytes.len())` of the
     parameter's two bindings. The mdtests that use `Slice<T>` as the
     example of a library enum (`library_field_accessors_*`,
     `a_library_field_function_of_a_constructed_value_*`) change meaning:
     `slice::len(slice::from_raw_parts(p, n))` is the component `n` with no
     unfold, an intended change each explained in the PR.
   - **2b-iii-d. Strings.** `str.interface.click` states `as_bytes` as
     `result == s` retyped (a cast between slice types keeps the count),
     mapped in the Rust front end's name table only. This finishes slice
     returns and `as_bytes`.
3. **Parameters and locals.** Slice parameters enter as one wide pointer;
   locals, assignments, reborrows, call arguments and returns carry it.
   Remove `spread_slice_arguments` and the paired-local paths. Migrate
   sidecars that compare pointers.
4. **split_at, iterators, chunks.** Their inputs and the slices they yield
   are wide pointers; their internal fields stay.
5. **Cleanup and docs.** `docs/reference/rust.md` (byte slices, string
   slices, pure-function slices, signatures), `docs/internals/kernel.md`,
   and `design/first-class-slices.md`, which this note supersedes.

## Open questions

- **Layout facts.** When to state rustc's two-word layout for a program
  that reads a stored wide pointer's words. Deferred until a program needs
  it.
- **`Box<[T]>`.** Its ownership of the allocation, beyond `owns` of the
  range, follows the existing `Box<T>` model; to be checked at step 3.
- **`dyn` pointers.** A vtable is a second kind of metadata. Out of scope;
  the form admits it without a new value kind.

## String slices

Decided 2026-11-25: `&str` is its own type, not `&[u8]`.

Rust's `str` is a byte sequence with one library invariant: its bytes are
valid UTF-8. `&str` is a wide pointer like `&[u8]`, with a byte count as
metadata. `len()` counts bytes, and `as_bytes()` returns the same pointer
and count. Every safe way to make a `str` keeps the invariant, and making a
non-UTF-8 `str` through `unsafe` (`str::from_utf8_unchecked`) is undefined
behavior.

So `&str` (`Str` in specs) is the same wide pointer form with its own type.
`as_bytes` is a retyping: the result equals `s`. The type is distinct so
that the UTF-8 invariant attaches to strings and never to arbitrary bytes.
That invariant is a validity predicate on the bytes in `s`'s range,
assumed for every `&str` a program receives and owed where one is built.
Until it is modeled it is not stated, and nothing is claimed about it.
Every fact proved about a string's bytes holds for the real `str`; what is
missing is only the one true fact about its encoding. Modeling it later
adds the predicate and changes no type.
