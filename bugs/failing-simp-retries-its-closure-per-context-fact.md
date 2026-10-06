# A failing `simp` retries its closure once per fact in its context

## Violated invariant

A smart tactic's failure must be prompt and bounded
(`AGENTS.md`, "Tooling stability comes first"). When `simp` cannot close a
goal, it runs its whole closure again on intermediate goals, a number of
times that grows with the facts connected to the goal's variables, and each
run repeats the closure's fallback routes. The miss costs work linear in
that context for every route the closure ends with, so adding or widening a
fallback route multiplies the cost of every failing `simp`.

Measured on 2026-10-05 with
`failing_simp_bound_selection_stays_linear_along_a_variable_chain` from
`src/surface/tests/scaling_tests.rs`: `requires 0 <= x0`, a chain
`x0 <= x1 <= ... <= xN`, `requires xN <= 100`, and the unprovable
`ensures x0 + 1 <= 50` proved by `execute(); simp();`. At `N` of 4, 8, 16,
and 32 the closure's last route, `simp closure: indexed bounds`, ran 44, 76,
140, and 268 times. Each run is constant work (it visits at most eight
variables), so the route's total is linear in `N` only because of the
retries: 118328, 280100, 526500, and 1019300 units of the tactic's 127565,
300253, 579237, and 1180213.

The retries predate that route. Before it followed bounds to a second
variable the same fixture took 91381, 174249, 350737, and 746721 units,
with the same number of closure runs.

The same breadth appears on the success side: on path `k` of a function's
early returns, simp's dependency selection reads all `k` conditions about
the goal's variable although its derivation cites one
(`bugs/early-return-paths-store-facts-whole.md`).

## Intended regression

A scaling test over the chain fixture that counts closure runs for the
failing goal, not only their total work: the count must not grow with `N`,
or must grow by a stated small bound. Keep
`failing_simp_bound_selection_stays_linear_along_a_variable_chain` as the
total-work check, and add a positive case (`ensures x0 + 1 <= 101`) that
still verifies, so the fix cannot be to give up earlier on provable goals.

## Acceptance criteria

- A failing `simp` runs its closure a number of times that does not grow
  with the facts connected to the goal's variables, or the growth is bounded
  by a documented constant.
- The fallback routes at the end of the closure run once per `simp`
  invocation on a given goal, not once per intermediate goal that repeats
  it.
- Goals `simp` closes today still close, with the same expansions.
- `scripts/check.sh` passes.
