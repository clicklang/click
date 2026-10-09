# Rust sidecars in Rust syntax

Status: accepted on 2026-10-08, not built. A Rust sidecar states its
signature in Rust syntax, and each language spells a place its own way
(`design/place-based-resource-clauses.md`). This document says what that
means and the order to build it in.

The rule behind every choice below: a Rust sidecar looks like Rust, and
Click's own words work the same in every language. `requires`, `ensures`,
`owns`, `views`, `consumes`, `produces`, `invariant`, `decreases`, `result`,
`old`, `forall`, the proof tactics and the resource declarations are not
respelled for Rust. What changes is everything the source language already
has a spelling for: signatures, types, places, casts and literals.

## What a Rust sidecar is today

The Rust source is unchanged and imported through Charon. Its sidecar is
written in C shape. From `examples/rust-slices`:

```rust
pub fn read(bytes: &[u8], index: usize) -> u8
pub fn write(bytes: &mut [u8], index: usize, value: u8)
```

```click
uint8 read(const uint8* bytes, uint64 bytes_len, uint64 index) {
    requires bytes_len <= 2147483647u64;
    requires index < bytes_len;
    views bytes[0..(int32)bytes_len];
    ensures result == bytes[(int32)index];
}
```

and from `examples/rust-field-borrow`, for `fn drop(&mut self)` in
`impl Drop for Guard<'_>` and `fn cleanup(value: &mut i32)`:

```click
void Guard_drop(struct Guard* self) { owns self->slot; owns self->slot[0..1]; ... }
void cleanup(int32* value) { owns value[0..1]; ensures value[0] == 42; }
```

The author has to know five translations that appear nowhere in the Rust:

1. A slice `&[T]` is two parameters, a pointer and `name_len`.
2. A reference `&mut T` is a pointer, and its referent is `value[0]` or
   `value[0..1]`.
3. Types are C names: `uint8`, `uint64` for `usize`, `void` for `()`.
4. A method is a free function named `Type_method`, and field access through
   `self` is `->`.
5. A range bound is `int32`, so a `usize` length is cast at every use:
   `(int32)bytes_len`, `(int32)(uint32)bytes_len`.

C++ had the first two for references and they were removed by making
"reference" a property of the parameter (`int32& value`; the name is the
referent). This proposal does the same for Rust.

## Proposal

### 1. The signature is the Rust signature

```click
fn read(bytes: &[u8], index: usize) -> u8 {
    requires bytes.len() <= 2147483647u64;
    requires index < bytes.len();
    views *bytes;
    ensures result == bytes[index];
}
```

A Rust sidecar declares a function with `fn name(params) -> T`. Parameter
types are Rust types: the integer types, `bool`, `()`, a declared struct by
name, `&T`, `&mut T`, `&[T]`, `&mut [T]`, `[T; N]`. Lifetimes may be written
and are ignored. (Arrays and lifetimes are not built yet.) The signature is checked against the imported function the
way a C sidecar's is checked against the C source, including mutability.

A C or C++ sidecar is unchanged. Which grammar applies is decided by the
`verifying` source's language, as the C++ reference syntax is.

### 2. A reference names what it refers to through `*`

For `value: &mut i32`:

| Meaning | Today | Proposed |
|---|---|---|
| the referent's value | `value[0]` | `*value` |
| owning the referent | `owns value[0..1]` | `owns *value` |
| a field, `p: &mut Cell` | `p->value` | `p.value` |
| owning a field | `owns p->value` | `owns p.value` |

`&T` is read authority and `&mut T` is ownership, but the clause is still
written: `views *value` or `owns *value`. Deriving the clause from the type
is a possible later step and is not proposed here; a contract that hands the
referent on, or returns less than it took, has to say so.

`p.value` follows Rust's automatic dereference. `->` is refused in a Rust
sidecar with the spelling to write.

### 3. A slice is one name

For `bytes: &[u8]`:

| Meaning | Today | Proposed |
|---|---|---|
| its length | `bytes_len` | `bytes.len()` |
| an element | `bytes[(int32)index]` | `bytes[index]` |
| the whole slice | `views bytes[0..(int32)bytes_len]` | `views *bytes` |
| part of it | `views bytes[a..b]` | `views bytes[a..b]` |

`*bytes` is the `[u8]` the reference refers to, as `*value` is the `i32`.
This answers the tracker's question of a spelling for a whole slice.

Underneath, the slice is still the pointer and length Charon delivers. The
two are carried by one parameter, the way a C++ reference parameter is
carried by a pointer named `&value`.

### 4. Indices are `usize`

`bytes[index]` and `bytes[a..b]` take a `usize` in a Rust sidecar without a
cast.

A place takes a 32-bit index today, and the contract has to say the length
fits one: `requires bytes.len() <= 2147483647u64`. An earlier version of
this section said the slice type could supply that bound, because a Rust
slice is at most `isize::MAX` bytes. That was wrong. `isize::MAX` is far
above what a 32-bit index reaches, so the bound is a limit of Click's memory
model that the contract states, not a fact about slices.

Two ways to remove the casts:

- **Surface only.** A `usize` parameter or a slice length written alone as
  an index or bound is converted, as the C-shaped `(int32)index` is. The
  bound stays a written `requires`, and any other `usize` expression is
  still cast where it is used. Small, and removes the casts from ordinary
  contracts.
- **Kernel.** Range bounds become mathematical integers or 64-bit terms.
  Removes the conversion and the bound everywhere and changes a hot
  representation; it needs the scaling regressions
  `docs/internals/verification-efficiency.md` asks for.

Decided: surface only first. It is built. The kernel change is what would
let a contract drop the bound, and is not scheduled.

### 5. Methods and receivers

```click
impl Drop for Guard {
    fn drop(&mut self) {
        owns self.slot;
        owns *self.slot;
        ...
    }
}
```

A method is declared inside `impl Type` or `impl Trait for Type` and its
receiver is `self`, `&self` or `&mut self`. `Guard_drop` stops being a name
an author writes. Tuple fields are `.0`, `.1`. An operator trait carries its
type argument, `impl MulAssign<u32> for U32X4`, which is how the importer
tells the implementations for one type apart.

### 6. Types and literals inside contracts

Types named in a contract or proof (`forall (k: usize)`, casts) are Rust
types, and a cast is `expr as T`. Literals take Rust suffixes (`4usize`).
`result` stays the name of the returned value.

## Order of work

Each step is a pull request that leaves every example verifying.

1. Done. `fn` signatures with scalar and struct parameters, Rust type names,
   `as` casts and literals. Both grammars are accepted for Rust sources
   during the migration.
2. Done, except the refusal. References: `*value`, `p.value`. `->` is still
   accepted, because the C-shaped sidecars use it; it is refused in step 5.
3. Done. Slices: one parameter, `.len()`, `*bytes`, `usize` indices by the
   surface-only route.
4. Done. `impl` blocks and `self`.
5. In part. The 16 Rust examples under `examples/` and their mirrored
   copies under `design/charon-trial` take their signatures from the Rust
   source and write `bytes.len()` and uncast ranges. Still to do: refuse
   `->` and the C-shaped grammar for Rust sources, and print Rust spellings
   in diagnostics and `click expand`, after the typed-index work.

Steps 1 to 3 are in pull request #435 and documented in `docs/reference/rust.md`, "Signatures in Rust syntax", with
fixtures under `tests/fixtures/rust-verification`.

## Decided

Accepted on 2026-10-08 as proposed:

1. Fields through a reference are `p.value`; `->` is refused in a Rust
   sidecar.
2. A whole slice is `*bytes`.
3. Clauses stay written for `&T` and `&mut T` parameters and are not derived
   from the type.
4. `usize` indices go by the surface-only route first; the kernel change
   follows only if proofs still carry conversions.
5. Methods are declared in `impl` blocks.

## Not covered

Generics and trait bounds in signatures, returned references, enums with
data, and closures follow what the Charon adapter supports
(`design/charon-trial/README.md`) and need no sidecar syntax until it does.
