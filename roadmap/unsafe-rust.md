# P2: Support unsafe Rust

Priority: P2.

Soundness: incomplete. The supported Rust slice excludes unsafe code
([the Rust reference](../docs/reference/rust.md)); unsupported syntax fails
during extraction or direct lowering, so no unsafe program is accepted today.
The risk this issue guards is the future one: unsafe Rust must not be admitted
by reusing C's rules where Rust's differ, in either direction.

## Motivation

Verified Rust code eventually reaches raw pointers: intrusive and linked
structures, FFI boundaries, `Vec`-style buffers, and the unsafe interior of
safe abstractions. Click should verify that code against Rust's rules, not
against C's.

## What carries over

All three languages lower into one kernel. The pointer value (address,
provenance and bounds; see
[pointer subobject bounds](../design/pointer-subobject-bounds.md)) and the
`owns`/`views` permission resources are shared. These already match Rust:

- provenance: a pointer reaches only the allocation it was derived from;
- arithmetic stays within an allocation or one past its end;
- address equality grants no access;
- integers carry no provenance. Click's lossless round-trip and checked
  low-bit tagging
  ([pointer integer representations](../design/pointer-integer-representations.md))
  correspond to Rust's strict-provenance `addr`, `with_addr` and `map_addr`.

## What unsafe Rust adds

1. **Bounds at formation.** A raw pointer derived through raw-pointer
   operations (`&raw const s.a`, `ptr::addr_of!`, casts of a whole-struct
   pointer) may move within its allocation. Whether a raw pointer derived
   from a reference to a field may leave that field depends on the aliasing
   model: Stacked Borrows forbids it, Tree Borrows permits access within the
   allocation. Click's member-bounds rule is C's reading. The Rust frontend
   must choose the bounds the adopted model gives each formation instead of
   applying C's rule. The pointer value already represents both.
2. **The aliasing model.** Stacked Borrows / Tree Borrows define when `&mut`
   is exclusive, what writes through raw pointers do to outstanding
   references, and the permissions of references created from raw pointers.
   This belongs to the permission layer (borrows, `owns`, `views`), not the
   pointer value. Choosing a model, or a subset that is sound under both,
   is the main decision here. The static parts map onto existing resources;
   dynamic permission tracking needs design.
3. **Exposed provenance.** `expose_provenance` and
   `with_exposed_provenance` require either an exposure model (a set of
   exposed live allocations an integer-to-pointer conversion may select) or
   an explicit refusal naming the API.
4. **Memory-level operations.** `MaybeUninit`, `transmute`, unions,
   `ptr::read`/`write`/`copy`, manual `drop`, and Rust's validity invariants
   (a `bool` holds 0 or 1, references are non-null and aligned). Most share
   the initialization and effective-type machinery with C and C++; the
   validity invariants are Rust-specific.

## Small intended regression

```rust
#[repr(C)]
pub struct Pair { pub a: u32, pub b: u32 }

// Valid Rust: the raw pointer is derived from a pointer to the whole
// `Pair`, so stepping to `b` stays within its allocation.
pub fn second(p: &mut Pair) -> u32 {
    let raw = p as *mut Pair as *mut u32;
    unsafe { *raw.add(1) }
}

// The raw pointer is derived from a reference to `a` alone. Stacked
// Borrows makes the read of `b` undefined; Tree Borrows permits it.
pub fn second_from_field(p: &mut Pair) -> u32 {
    let raw = &mut p.a as *mut u32;
    unsafe { *raw.add(1) }
}
```

`second` must verify `result == p.b`. `second_from_field` follows the adopted
aliasing model: refused at the read, naming the field the pointer was derived
from, unless Click adopts Tree Borrows' rule for it.

## Dependencies

- The shared [object and memory laws](../design/cpp-object-model.md#decisions-and-scope)
  and [current native-interface evidence](../design/object-model-current-audit.md#native-interface-evidence-matrix)
  constrain this work.
- Raw pointers stored in struct fields build on the loaded-pointer
  representation, which has landed for C: a pointer read from memory is named
  by that read ([propositions](../docs/concepts/propositions.md),
  [equality closure](../docs/internals/equality-closure.md); for example
  `mdtests/a_read_through_an_equal_loaded_pointer_reaches_its_uint64_field.md`).

## Acceptance criteria

- A decision on the aliasing model, recorded in the Rust reference: Stacked
  Borrows, Tree Borrows, or a stated subset sound under both.
- Raw pointers are formed with that model's bounds. Both functions above
  behave as the decision states, in fresh, expanded and rewritten checking.
- A documented aliasing-model subset: which reference and raw-pointer
  interactions are supported, each with an accepting and a refusing
  regression, and an explicit refusal for the rest.
- Exposed-provenance APIs are either modeled or refused with a diagnostic
  naming the API.
- `docs/reference/rust.md` states the supported unsafe subset and its limits.
