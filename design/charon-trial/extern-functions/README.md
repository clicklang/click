# Calls to an `extern` block function

`ffi.rs` declares `clamp_reading` in an `unsafe extern "C"` block as a
`safe fn`, so `caller` calls it without `unsafe`. Charon writes the
declaration as a C-ABI function with an `Extern` body and no parameter names.
The importer records it as an `external` function with positional
parameters, and lowering gives it an interface and no body, as for a C
`extern` declaration.

The sidecar states the contract Click trusts with
`extern fn extern_functions::clamp_reading(raw: i32) -> i32`, whose head
names the parameters and must have the declaration's exact types. `caller`
must establish its `requires` and may use its `ensures`. Regressions refuse a
caller that cannot establish the precondition, a postcondition the caller
cannot meet from the contract, a head with other types, and a verified `fn`
for the bodiless declaration.

`unsafe fn` items and other ABIs are refused, since their calls need
`unsafe`.
