# Capturing closures passed as `&dyn Fn`

`closure.rs` passes closures to `shift` and `increment`, which take a
`&dyn Fn(i32) -> i32` and call through it. `caller`'s closure borrows `k`,
`moved`'s copies `m`, and `plain`'s captures nothing. Charon writes a
closure as a state type whose fields are its captures, a `Fn::call` method
reading them through `self`, and an unsizing cast of a reference to the
state. The importer keeps the `call` body as a function whose leading
parameters are the captures, and reads the cast as the creation of a
function value from the captured values. A closure that captures nothing
is its function's address.

The sidecar names a closure as rustc does, `capturing_closures::caller::
{closure#0}`, with only the closure's own parameters in the head; its
contract reads the captures by name, `ensures result == y + k;`. `shift`
requires the parameterized contract `Adds(f, { amount: k })`. Creating a
closure gives a function value carrying the closure's contract fixed to its
captured values, and the call to `shift` checks that contract refines
`Adds` with the caller's facts about those values.

Regressions refuse a closure contract weaker than `Adds`, one requiring
more than `Adds` gives, a callee fixing `amount` to another value, a false
closure contract, and a capture-free closure that does not meet
`Increments`. One variant drops `Adds`'s bound on `amount`, so `caller`'s
closure gets its bound on `k` from the caller's facts.
