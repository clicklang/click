# A named contract with a value parameter

`adds.rs` passes `add3` to `apply`, which calls through a `fn(i32) -> i32`.
The sidecar's contract `Adds` declares a value parameter with `let amount:
i32;`, and `apply` requires `Adds(f, { amount: k })`: a call through `f`
returns its argument plus `k`. At `caller`, Click checks `add3`'s contract
against `Adds` with `amount` fixed to `3`.
