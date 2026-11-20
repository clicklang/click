# Place-based resource clauses

Resource clauses name source-language places or ranges of places. The accepted
October 2026 migration is complete. The
[C resource-clause reference](../docs/reference/language/c.md)
and [Rust reference](../docs/reference/rust.md#signatures-in-rust-syntax)
describe the current syntax and checked fixtures.

## Places and ranges

A bare place names its own storage: a variable, field, element or dereference.
For a pointer, `owns p` names its slot and `owns *p` names its referent.
A pointer parameter's private slot cannot be transferred by its caller;
the contract must name the referent instead.

A range requires a pointer or array and counts elements of that type. A
struct-pointer range counts structs, rather than the historical four-byte
cells. `&place`, `object(p)` and ranges on scalar fields were retired and
are refused with their replacements. Use a field, `*p`, or a typed range.
Wide symbolic struct ranges have since gained the bounded support described in
[Allocation sizes](heap-allocation-sizes.md); the original migration's blanket refusal is
not a current support statement.

C++ reference parameters name the referent directly; Rust references use `*r`
and automatic field dereference, `r.field`. C++ receivers use `this`.
Rust slices carry their length and support whole-slice clauses. These
spellings do not derive permission from the native type: resource clauses
still state the required authority.

Place lowering uses the admitted layout. C++ base-tail padding and Rust's
compiler-selected field layouts cannot be inferred from a handwritten cell
count. Storage, initialization and authority remain separate obligations.

Diagnostics print the source place when one exists, including nested fields,
pointer chains and array elements. A range spanning unrelated fields may
still need byte offsets; it must not be mislabeled as a single field.

## Reference locals

Scalar C++ reference locals use a carrying pointer named `&r`, so a proof
reads the referent as `r` and its address as `&r`. Binding a reference is not
an assignment; `assignment(r, N)` is refused. Struct/class reference locals
carry the same address and retain their nominal layout: `r.field` reads a
field of the referent and `&r` names its address. They introduce no ownership,
copy, or destruction of that object; reads and writes use the caller's held
permissions. Pointer-based bindings check the entire record's live storage
without loading fields. Struct/class reference results retain the same nominal
layout through calls: `result.field` reads a field and `&result` names the
returned address. A local binding to that result keeps the existing reference
carrier and permissions. See [supported C++](../docs/reference/cli/capture.md).

## Decisions and history

Reading at another width uses the checked byte representation or an explicit
load, rather than a second width annotation on resource ranges. The
[specification rulings](proof-language-rulings.md) retain the decision.

The [original migration record](https://github.com/clicklang/click/blob/2175760b9/design/place-based-resource-clauses.md)
contains the old acceptance table, corpus counts and implementation sequence.
Those pre-migration refusals and counts are not current behavior.
