# Typed method resolution

Status: steps 1 and 2 implemented. Every slice method, index and subslice,
on a slice value or a slice parameter, goes through the one resolution in
declaration expansion. Step 3 remains.

## Problem

Click's own types have methods: a Rust sidecar writes Rust's methods on
values, `s.len()`, `s.as_ptr()`, `s[i]`, `s[a..b]`, and a C or C++ sidecar
may hold the same Click values, such as a theorem binder of type
`Slice<uint8>` or a library `Vec`. Today the parser rewrites each one as it reads it, into
the library call or subslice that means it, such as `slice::len(s)`. So the
parser has to know the receiver's type from the text alone. It knows it for:

- a slice parameter (`bytes`), from the signature;
- a call of a function declared to return `&[T]` (`half(bytes)`);
- a written subslice or constructor;
- a theorem binder with a written slice type.

It does not know it for a value whose type comes from type inference:

- a `match` arm binder, `Option::Some(s) => s.len()`, typed by the
  scrutinee's type;
- a `let` binder, `let s = half(bytes); s.len()`, typed by its value.

Both fail to parse today. The explicit library call, `slice::len(s)`, works
on the same binder, because type validation knows `s` is a `Slice<u8>`.

Every library type with Rust methods will hit the same wall: `Vec`
(`v.len()`, `v[i]`), `Option` (`o.is_some()`), and the iterator model
(`iter.len()`, `chunks.remainder()`). Teaching the parser each type's
methods, and enough type inference to know its receivers, does not scale.

## Principle

A method means what the receiver's type says it means. The parser records
a method call as written; the meaning is chosen once types are known, by
one rule for every receiver, however the receiver was introduced.

## Design

### Surface form

The parser reads `x.m(args)` as a method call node,
`ContractExpression::MethodCall { receiver, method, arguments }`, in every
sidecar language, whenever the receiver is not one whose C or C++ type the
parser already knows. Indexing `x[i]` and `x[a..b]` on such a receiver keep
their own forms, an index and a range index, with the receiver unresolved.

The forms whose meaning comes from declarations the parser has already read
do not change: `p->f` and `s.f` on a C struct or union, resource fields, and
a C++ member access on a receiver of a known class type. In C, `s.f(args)`
on a struct is a call through a function-pointer field, and in C++ it can
be a member function; those receivers have C or C++ types, so they stay
with the parser. A method call is a receiver of a Click type: a slice, an
enum, a library `type`, or a binder of one.

### Resolution

Resolution maps a method on a receiver type to a library function, by a
table keyed by the type and the method name:

| Receiver type | Method | Means |
|---|---|---|
| `Slice<T>` | `len()` | `slice::len(x)` |
| `Slice<T>` | `as_ptr()` | `slice::as_ptr(x)` |
| `Slice<T>` | `[i]` | `slice::as_ptr(x)[i]` |
| `Slice<T>` | `[a..b]` | the subslice, `Slice::Slice(slice::as_ptr(x) + a, slice::subslice_len(a, b, slice::len(x)))` |

A library type adds rows, not parser code. A method a library declares
for its type (`impl` functions on a library `type`, such as `Vec`) is
resolved the same way, by its declaring type.

Declaration expansion resolves a `MethodCall` before validation, where
constructor type inference already knows the type of every name in scope
(`ConstructorTypes::known_type`: parameters, `match` arm and `let`
binders, pure-function results, written constructors). It rewrites the
call into the explicit form the table names, so validation and lowering see
only library calls, indexes and constructors. A receiver whose type has no
such method is refused with the type and the method:
"`Slice<uint8>` has no method `size`". An index `x[i]` on a receiver of a
non-algebraic type, such as a sequence, stays the index it was.

The definitional reductions stay: `.len()` and `.as_ptr()` of a
constructed slice reduce to its fields as they are lowered, so a subslice's
length needs no `unfold` (#2497).

### Slice parameters

A slice parameter is still lowered as a pointer and a length
(`design/first-class-slices.md`, "Representation by position"). Where it is
read as a slice, in a subslice `bytes[a..b]`, the parser writes the slice
value it stands for, `Slice::Slice(bytes, bytes_len)`, as the receiver, and
resolution's constructor rule reduces its methods to the pair. A slice value
passed to a slice parameter of a pure function is spread into its methods
`as_ptr()` and `len()`, resolved the same way. `bytes.len()` and `bytes[i]`
on a parameter keep their direct spellings, the length variable and the read
through the pointer, which are the same values.

### Printing

A `MethodCall` prints as written, `s.len()`. A resolved library call
prints as the method on its receiver where the receiver is a Rust value, as
`slice_call_spelling` does today, so a fact reads back through the same
resolution.

## Cost

Resolution is one table lookup per method call, on a type the checker has
already inferred. It adds no search and reads no facts, so lowering stays
fact-stable.

## Migration

1. `MethodCall` and range-index forms in the parser for receivers it cannot
   place, in Rust, C and C++ sidecars, resolved by type in validation and
   lowering, with the slice rows. `match` and `let` binders work, and a C
   theorem over a `Slice<uint8>` writes `s.len()`. The eager parser
   rewrites stay.
2. Move the parser's eager slice rewrites onto the same table, and delete
   them.
3. `Vec`'s and the iterator model's methods as rows of the table, when those
   types land.

## Open questions

1. **User-declared methods.** Spec functions declared in an `impl` block on
   a crate type could join the table. That is deferred until a proof needs
   it.
