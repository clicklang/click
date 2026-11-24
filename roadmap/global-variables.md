# Extend static-storage initializers and string-literal coverage

Priority: P2.

Soundness: incomplete. The forms listed under "Deferred language coverage"
are refused by the C frontend; no false acceptance is known. Static storage
is initialized once at program startup and ordinary function entry does not
restore initializers, which `global_entry_initializer_rejected.md` and
`static_entry_initializer_rejected.md` protect (`fail: stale_initializer`).

File-scope objects, statics and basic string literals are delivered; this
item keeps the broader initializer and literal coverage. The const
callback-suite proof for real augmentation callbacks is rbtree launch work,
chunk 14 of [rbtree-example.md](rbtree-example.md).

## Violated invariant

Click should accept every valid C static initializer whose values are
integer constant expressions or link-time addresses, placing each cell where
the C rules (C11 6.7.9) and the target ABI put it. The forms below are valid
C that Click refuses.

## Intended regression

A file-scope `struct state entries[] = { [2] = { 7 } };` whose `main` returns
`entries[2].value` verifies with `sizeof(entries)` equal to three ABI struct
sizes, next to a passing `int32 grid[2][3] = { [1][2] = 5 };` and a basic
`L"ab"` literal with a stated element type. Each currently fails with a
located refusal.

## Delivered scope

| Delivered capability | Representative evidence in `mdtests/` |
| --- | --- |
| Stable scalar globals, cross-file extern linkage, private statics and ordinary current-value contracts | `file_scope_globals.md`, `file_scope_static_arrays.md`, `global_entry_requires_current_value.md`, `file_scope_global_link_errors.md`, `file_scope_static_link_errors.md` |
| Data-only translation units, typed objects and relocations | `data_only_translation_unit.md`, `data_only_duplicate_definition.md`, `data_only_private_not_external.md` |
| Tentative-definition coalescing, incomplete extern arrays and compatible shape resolution | `file_scope_tentative_globals.md`, `file_scope_tentative_arrays.md`, `file_scope_tentative_aggregates.md`, `file_scope_incomplete_extern_arrays.md`, and their link-error regressions |
| Fixed/inferred scalar arrays, supported multidimensional shapes and one-dimensional struct arrays | `aggregate_static_objects.md`, `initialized_aggregate_static_objects.md`, `initialized_aggregate_static_arrays.md`, `file_scope_multidimensional_arrays.md`, `file_scope_inferred_multidimensional_array_bounds.md`, `file_scope_static_inferred_multidimensional_array_bounds.md`, `static_array_parity_aggregate.md`, `static_array_parity_scalar.md`, `static_array_parity_multidimensional.md`, `static_array_parity_fixed_multidimensional.md` |
| Constant-expression initialization, selected conditional branches, casts and supported designators | `static_integer_constant_initializers.md`, `static_integer_constant_expression_control.md`, `designated_aggregate_static_objects.md`, `designated_scalar_static_arrays.md`, `a_file_scope_inferred_array_takes_designators.md`, `a_designated_inferred_array_has_the_largest_index_plus_one_elements.md` |
| Const storage and callback-table dispatch/refinement | `const_global_table.md`, `const_aggregate_objects.md`, `const_callback_table_dispatch.md`, `const_callback_table_abstract.md`, and their write/signature rejection fixtures |
| Function-local static storage and ownership transfer without initializer reset | `static_scalar_locals.md`, `static_local_arrays.md`, `program_entry_static_ownership.md`, `private_state_mutation_reset.md`, `private_state_wide_return.md` |
| Resources over globals and private objects from several files | `qualified_static_resource.md`, `qualified_static_ownership.md`, `qualified_static_struct.md`, `qualified_function_static_ownership.md` |
| Stable object/subobject address initializers | `static_subobject_pointer_initializers_cross_file.md`, `static_initializer_dependency_chain_cross_file.md`, `static_pointer_initializer_const_discard.md`, `static_pointer_initializers_cross_file.md`, `a_linked_pointer_initializer_names_a_private_object_of_its_defining_file.md` |
| Basic ASCII strings, supported escapes, adjacent-literal concatenation, read-only storage and call propagation | `string_literals.md`, `string_literals_call.md`, `string_literals_reject_write.md`, `concatenated_string_literals.md`, `concatenated_string_literals_rejected.md` |

Implementation evidence includes the declaration/linking/constant-initializer
and string-literal tests in `src/languages/c/tests.rs`, static initialization
in `src/kernel/functions.rs`, and
`src/kernel/functions/program_entry_tests.rs`.

Do not restore initializer values at ordinary function entry to make a
caller pass: a parameterless `main` proof receives initialized writable
ownership and const views, and ordinary contracts describe current state with
`old(...)` for entry state. Callbacks in const tables are read through
`views`, never `owns`; do not mint write authority for const cells.

## Deferred language coverage

Supported today ([Supported C](../docs/reference/language/c.md)): integer
constant-expression designators, including enumeration constants, in
one-dimensional scalar arrays, with the bound inferred as one past the
largest index; and literal `[n] = {...}` designators in one-dimensional
aggregate arrays with an explicit bound. Still refused:

- Element designators in an aggregate array with an inferred bound, and
  non-literal designator expressions in aggregate initializers.
- Designators on multidimensional arrays, flat or designated initializers
  for inferred multidimensional arrays, multidimensional aggregate arrays,
  designated initializers for inline scalar array members, and empty
  initializers of inferred arrays. Preserve shape, linkage identity, ABI stride and one-time
  initialization; unresolved extern declarations stay rejected.
- File-scope `static` incomplete arrays without a complete definition in the
  same translation unit, and unresolved incomplete tentative definitions.
- Wide and prefixed literals, non-ASCII characters and unsupported escapes,
  with explicit element types and encoding semantics.

Calls or runtime loads in C static initializers remain invalid; this item
does not authorize accepting them or adding C++ dynamic startup.

## Acceptance criteria for the retained P2 work

Use small unchanged C fixtures for each chosen extension. Verify initial values
at actual startup (for example, a supported `main` returning `table[2]`), or
state current-value preconditions at ordinary entry; then cover retained state
across calls. Preserve duplicate-definition, incompatible-shape, unknown-name,
const-write, ownership and stale-initializer rejection tests. Keep syntax-only
coverage distinct from passing program proofs and from known negative caller
fixtures. Run focused tests and the full unpiped `scripts/check.sh`; update
[Supported C](../docs/reference/language/c.md) as each supported boundary grows.
