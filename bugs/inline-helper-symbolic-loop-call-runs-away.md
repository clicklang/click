# A call to an inline helper with a symbolic loop runs away instead of failing

## Violated invariant

A tactic that cannot finish fails promptly, within its deterministic work
budget, with a local diagnostic (`AGENTS.md`, "Tooling stability comes
first"). Counted work tracks real cost, so the default budget bounds time and
memory.

Executing a call to a `static inline` helper whose body holds a loop with a
symbolic guard does neither, when the helper has no Click contract. The call
executes the helper's body at the call site, the body's `while` is
unrolled symbolically, and time and memory grow far faster than the counted
work. Under the default `--work-limit` the run does not stop: it held 15 GB
after two minutes and was killed.

## Reproduction

`mdtests/inline_helper_contract_is_the_call_boundary.md` with the helper's
sidecar contract (and proof) removed, so the call runs the body. With the
contract, the same call applies it in one step and finishes promptly. The
caller's proof stays
`execute(); simp();`. Measured on that equivalent setup before inline helpers
applied their contracts, on a release build, one run at a time, with
`--work-limit W`:

| W (units) | wall time | peak memory |
| --- | --- | --- |
| 50,000 | 0.25 s | 0.10 GB |
| 100,000 | 2.6 s | 0.64 GB |
| 150,000 | 7.2 s | 1.7 GB |
| 200,000 | 13.9 s | 3.4 GB |
| 300,000 | over 30 s | over 8 GB (stopped by a memory cap) |

Doubling the counted work multiplies time and memory by about five. `click
profile --work-limit 150000` charges all of it to the one `execute` and the
nested operation `verification statement: call assign`.

The loop unroller is `execute_c_while_paths` in
`src/kernel/eval/statements.rs`. Each pending iteration rebuilds its
assumptions from the facts the path accumulated so far
(`assumptions_with_path_context`), so the copying alone is quadratic in the
iteration count, and the unroll limit (`loop_unrolls: 256`) bounds iterations,
not the work each one does. Which of these dominates has not been measured.

The rbtree insert no longer reaches this: `__rb_insert` has a verified
contract, so `rb_insert_color`'s call applies it. A contract-less Linux helper
with a loop would.

## Intended regression

The reproduction above as a negative mdtest, refused within the default budget
in well under a second, plus a scaling test that runs the call at two or three
unroll limits and bounds the growth in counted work, wall time, and peak
memory together.

## Acceptance criteria

- The reproduction fails promptly under the default work limit. The
  diagnostic names the helper's loop and says it cannot be decided at the
  call site, or reports an exhausted budget that charged the real cost.
- Counted work over a symbolic unroll grows with its real cost, checked over
  several sizes as `docs/internals/verification-efficiency.md` requires.
- Concrete unrolls, such as `mdtests/inline_helper_ranked_loop.md` itself,
  still verify.
