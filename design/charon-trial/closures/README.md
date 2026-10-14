# Closures passed for a function pointer

`closure.rs` passes closures that capture nothing, `|y| y + y`, to `apply`,
which takes a `fn(i32) -> i32` and calls through it. Charon writes such a
closure as a state type with no fields, the `call`, `call_mut` and
`call_once` methods of its `Fn` traits, and a generated `ClosureAsFn`
function that the pointer cast names. The importer keeps the `Fn::call`
body as the closure, rewritten as a function of the closure's parameters,
and reads the cast of the generated function as the closure's address.

The sidecar names a closure as rustc does, by its enclosing function and its
index there, `fn closures::caller::{closure#0}(y: i32) -> i32`, and verifies
it like any function. `apply` requires the named contract `Doubling` of its
pointer, so a caller passing a closure must show the closure meets
`Doubling`, from the closure's own contract. `choose` passes a different
closure on each branch, `{closure#0}` and `{closure#1}`.

Regressions refuse a closure contract that does not meet `Doubling`, a false
closure contract, a caller whose closure has no contract, and a closure name
the program does not define.
