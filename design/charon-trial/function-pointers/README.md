# Calls through a function pointer

`callback.rs` passes the function item `twice`, reified as `fn(i32) -> i32`,
to `apply`, which calls through the pointer. Charon writes the reification as a
`CastKind::FnPtr` of `const twice` and the call as a `FnOperand::Dynamic` call
through a local. The importer records them as a `function_address` value and a
`through_pointer` call, and lowering uses the kernel's indirect call, as for a
C callback.

`relay` forwards its own pointer parameter to `apply`, a copy of the pointer
value, and `forward` passes `twice` to `relay`.

The sidecar gives the pointer a named contract, `contract fn Doubling(x: i32)
-> i32`, which `apply` requires of `f`. At `caller`, Click checks that `twice`
meets `Doubling` from `twice`'s own contract. Regressions refuse `apply`
without `requires Doubling(f)`, `relay` without the contract it forwards, a `twice` whose contract does not meet
`Doubling`, and a `Doubling` that `apply` cannot establish.
