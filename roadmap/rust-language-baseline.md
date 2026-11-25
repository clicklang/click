# A Rust language baseline that ordinary small crates meet

Soundness: incomplete. Click refuses ordinary safe Rust that it should
accept: any function that takes or returns `&str` or `String`, generic code
bounded by a trait other than `Copy`, and most standard-library calls. These
are refusals with diagnostics; no false acceptance is known.

## Ruling and scope

Maintainer direction, 2026-11-24: launch needs a minimum Rust language and
standard-library baseline, not only installation and dependencies
([rust-support.md](rust-support.md)). A Rust user's first function usually
takes a `&str`, and a dependency's API usually involves strings, generics or
traits. Without this baseline the installed front end and Cargo dependencies
reach code Click refuses within minutes.

The target is a small, ordinary crate: safe Rust, `panic=abort`, no
concurrency, no floats. The [pointer model](../design/pointer-model.md#rust-raw-pointers)
describes the constraints on unsafe Rust.
Broader coverage beyond this baseline stays post-launch, as described in the
[Rust reference](../docs/reference/rust.md).

## Today

The [coverage matrix](../docs/reference/coverage.md) and the
[Rust reference](../docs/reference/rust.md#supported-semantics) give the
current subset: integer scalars except 128-bit, `bool`, structs, enums and
`match`, `Option`, `Result`, `Box`, slices, fixed arrays, `Vec`, loops over
ranges, slices and a few iterators, closures and trait objects of scalars,
crate traits, and generics whose type parameters are bound by nothing but
`Copy`. The standard library has interfaces in `library/rust/` for the
integers, `Option`, `Result`, slices and `Vec`, and for `str::len` and
`str::is_empty`. A `&str` parameter is read as a shared byte slice
([string slices](../docs/reference/rust.md#string-slices)); `String`, string
literals, `as_bytes` and `==` are not supported yet. `as_bytes` needs a
function that returns a slice, which no Rust function can yet, and `==` a
call of the core `PartialEq` trait on a non-scalar type.

## Requirements

1. **`&str` and `String`.** Follow the [library-interface
   rule](../docs/concepts/library-interfaces.md): `str` and `String` are
   library types with interfaces in `library/rust/`, modeled the way `Vec<T>`
   is (`library/rust/vec.click`) as a finite byte sequence. UTF-8 validity is
   a predicate on that sequence, assumed for every `str` and `String` value
   and stated by the interface, not re-proved by verified code. At least:
   string literals; `len`, `is_empty`, `as_bytes` and equality; `String::new`,
   `String::from(&str)`, `push_str`, `push` of an ASCII `char`, `as_str`, and
   borrowing a `String` as `&str`; moves and drops as for `Vec`. Methods that
   split at a byte index owe Rust's char-boundary panic check.
2. **Generics with standard trait bounds.** A generic function or impl whose
   type parameters are bound by `PartialEq`, `Eq`, `PartialOrd`, `Ord` or
   `Clone` verifies once for every type, as `Copy`-bound generics do today,
   with each bound's methods reached through its core trait's interface. An
   instance at a supported type checks its call sites against that interface.
3. **Standard-library calls a small crate makes.** Interfaces for the
   methods the regression crate below and the dependency demonstration in
   [rust-support.md](rust-support.md#requirements) call, chosen by those two
   programs rather than by a list made in advance. Each is added through the
   [`library-interface` skill](../.agents/skills/library-interface/SKILL.md).

## Intended regression

A committed small crate under `examples/`, written as ordinary Rust rather
than shaped for the verifier, that parses and summarizes text: for example a
word or token counter over a `&str` that returns a `Vec` of `(String, usize)`
pairs, with a generic helper bounded by `Ord`. Its sidecar proves panic
freedom and one functional property per public function. The test locks it,
verifies it offline with the front end removed, and checks refusals for a
byte-index split that is not on a char boundary and for a call to a `str`
method that has no interface.

## Violated invariant

An ordinary small safe-Rust crate that handles text and uses standard trait
bounds imports and verifies; its standard-library calls are seen only through
Click interfaces.

## Acceptance criteria

- `library/rust/` has `str` and `String` interfaces with the operations in
  requirement 1, and the coverage matrix's "Strings" row is no longer "Not
  supported".
- Generic code bounded by `PartialEq`, `Eq`, `PartialOrd`, `Ord` or `Clone`
  verifies for every type, with a refusal test for a bound outside the list.
- The regression crate and its refusals pass in the gate.
- The Rust reference and coverage matrix describe strings, the trait bounds,
  and the added standard-library methods, each with a checked example.
