# A chain of N sequential branches is quadratic and overflows the stack

Soundness: not soundness. This is a performance and crash defect: the
verifier spends time quadratic in the number of sequential `if` statements
and, past about 200 of them, aborts with a stack overflow. No claim that
should be refused verifies.

## Violated invariant

Simple checking must scale with the selected source and the state it changes
(`docs/internals/verification-efficiency.md`). A function of N independent
`if (a_i > 0) { s = s + 1; }` statements, each proved by one `step();`,
should verify in time roughly linear in N, and must not crash.

## Reproduction

`scripts/step-scaling-hunt.py`'s `branches` shape, with the profiling build:

```sh
cargo build --profile profiling --bin click
python3 scripts/step-scaling-hunt.py branches --sizes 32,64,128
```

Then generate N = 192 and 256 the same way (`SHAPES["branches"](n)`) and run
`target/profiling/click verify` on each. On master at `8d8a621c`:

| N   | whole verification | charged step work (total) |
|-----|--------------------|---------------------------|
| 32  | 0.45 s             | 1,810                     |
| 64  | 1.21 s             | 3,506                     |
| 128 | 3.64 s             | 6,898                     |
| 192 | 8.14 s             | —                         |
| 256 | stack overflow on the main thread (`RUST_MIN_STACK` does not help) | — |

Charged work stays linear while time grows with exponent about 2 (×2.24 from
128 to 192), so the quadratic cost is uncharged: the work budget cannot see
it, and the step-shape gate (`a_branch_arm_step_ignores_earlier_branches`)
passes. The overflow points to a recursion whose depth grows with the number
of earlier branches, most likely over the joined value of `s`, whose term
nests one conditional per branch.

## Acceptance criteria

- `branches` at N = 256 and 512 verifies without a stack overflow.
- Whole verification time grows at most about ×2.3 per doubling of N from 64
  to 256.
- A deterministic regression charges the work that grows (or removes it), so
  a scaling test fails on the current behavior.
