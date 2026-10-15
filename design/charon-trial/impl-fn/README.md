# Closures and function items passed for `impl Fn`

`closure.rs` passes callables to `shift` and `both`, which take `impl
Fn(i32) -> i32` parameters, and to `apply`, which takes a type parameter
`F: Fn(i32) -> i32`. `caller`'s closure borrows `k`; `plain`'s captures
nothing; `named` passes the function item `inc`; `twice` passes two
closures to `both`, which composes them.

Charon writes the callee as a generic function whose type parameter has an
`Fn` clause and an output type constraint, and a call through the parameter
as `TraitClause::call(&f, (x,))`. The importer reads the parameter as a
callable value of the clause's signature and the call as a call through it.
The caller passes the closure's state by value, or the function item's
`FnDef` constant, with the callee instantiated at that type; the state is
the closure's creation, as for `&dyn Fn`, and the constant is the item's
address.

The sidecar writes each head as the source does, `f: impl Fn(i32) -> i32`
and `apply<F: Fn(i32) -> i32>(f: F, x: i32)`. `Adds` states the bounds of
its result, so `both` can pass `f(x)` to `g` without deriving a bound from
`result == x + amount`.

Regressions refuse a closure contract weaker than `Adds`, a function item
that does not meet `Increments`, a call through a callable with no
contract, a false closure contract, and a type parameter bound that differs
from the contract's type.
