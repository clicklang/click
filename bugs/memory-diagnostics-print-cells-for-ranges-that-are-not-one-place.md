# Memory diagnostics print cells for a range that is not exactly one place

## Violated invariant

A resource clause names a place, so a diagnostic about memory names it the
way a clause would. Since #393 a missing or held fact that is exactly one
field or one whole struct prints as `p->field` or `*p`. A fact that is
anything else still prints four-byte cells counted from a struct pointer,
which no clause can be written with: `p[1..2]` on a struct pointer now means
a whole struct.

## Reproduction

`mdtests/contract_field_bearing_instance_views_grant_no_write.md` reports

```
missing resource fact `owns node->right`
held `owns node->right[4..6]` covers `node->right` only when
`((load(node[2]) - …) + 4) <= 2` and `3 <= ((load(node[2]) - …) + 6)`
```

The missing fact is a place. The bounds in the note are cells, and
`load(node[2])` is the third cell of `node`, not a field.

A second form: a step that reports an obligation prints

```
Requires produces owns p[1..2]
```

for the second `int32` behind an `int32* p`, where the fact beside it prints
`owns p[1]`
(`authority_consuming_helper_cannot_return_the_wrong_private_body` in
`src/surface/tests/authority_private_body_tests.rs`).

## Cause

`describe_memory_range` in `src/surface/diagnostics.rs` tries
`describe_struct_place_range` first, which answers only for a range that is
exactly a field's slot, a leaf of an embedded struct, or the whole struct.
Everything else falls through to `describe_parameter_relative_range`. The
"covers only when" note is built from the raw endpoints by
`describe_missing_range_end_note`, and the obligation line is built by a
separate printer in `src/surface/proof/proof_object/step_application.rs`.

## Intended regression

A unit test beside `a_missing_memory_fact_is_reported_as_a_place` in
`src/surface/tests/surface_syntax.rs` for a range that covers two adjacent
fields, a range that covers part of an embedded struct, and the note for a
held pointee range.

## Acceptance

- A range over several whole fields prints as those fields.
- A load used as a bound prints as the field it reads (`node->right`), not as
  a cell of the struct.
- The obligation line and the fact beside it print the same place the same
  way.
- No diagnostic prints `p[a..b]` for a struct pointer `p` unless it means `b - a`
  structs.
