# Signature diagnostics omit pointer constness

## Violated invariant

A signature mismatch diagnostic must display the qualification that differs.
When a Rust shared reference requires a const pointer, displaying identical
expected and actual parameter types hides the reason for rejection.

## Reproduction

While adding `tests/rust_import/crate_inputs.rs`, the inherent `Value::read`
sidecar initially declared `struct Value* self` instead of `const struct
Value* self`. Verification correctly rejected it, but displayed both sides
as the same `struct __rust_q_I4_demo_I5_Value* self`.

To reproduce, remove `const` from that test's method parameter and run
`rust_crate_locks_all_compiler_inputs_and_preserves_qualified_calls` with pinned
Charon. The failure is at signature checking, before its proof executes.

`src/surface/verification.rs` compares `pointee_is_constant()` but calls
`describe_parameter_type()` without that qualification when rendering the error.

## Acceptance criteria

- Expected and actual parameter renderings include their pointer constness.
- A small shared-reference regression distinguishes const and mutable pointer
  spellings in the diagnostic, including a struct pointer.
- Signature acceptance and the execution/authority rules are unchanged.
