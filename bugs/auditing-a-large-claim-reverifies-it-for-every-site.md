# Auditing a large claim re-verifies the whole claim for every site

## Violated invariant

A tool's cost must scale with the selected syntax and the output it produces
(`AGENTS.md`, "Scalable verification is a correctness requirement").
`click audit` instead costs the number of smart sites in a claim times the
cost of verifying that whole claim, twice over.

For each site the audit expands the site, which runs the whole claim with
capture. `__rb_insert.contract` in
`examples/rbtree-insert/rbtree_insert.click` has 190 smart sites and takes
about 16 million work units to verify. Measured on a release build, every
site costs the same whatever it is:

| phase | work units | wall time |
| --- | --- | --- |
| expand one site | 17.2 million | 32 s |
| re-expand | 1.6 million | 1 s |

That is about 33 seconds a site, so about 105 minutes for the claim, at the
edge of the audit's own 110-minute run limit. The first site of a claim also
runs two cold verifications, about 32 seconds each. The audit of this example
has never been seen to complete.

The audit used to verify each site's rewrite in its retained session as
well, another whole-claim run per site. It now applies a claim's rewrites
together and verifies the claim once, so that part no longer scales with the
sites. Expansion remains: the capture selects one source tactic per run, so
expanding `n` sites of a claim still runs the claim `n` times.

Memory is no longer part of this either. The retained session used to keep
every check's kernel state, about 1.1 GB a site here; it now restores its
baseline before each check
(`retained_session_checks_leave_no_kernel_state_behind`).

## Reproduction

Under a memory cap, on a release build:

```sh
cd examples
systemd-run --user --scope -q -p MemoryMax=14G -p MemorySwapMax=0 \
    ../target/release/click audit --verbose \
    --start-at rbtree-insert/rbtree_insert.click:LINE:1 \
    rbtree-insert/rbtree_insert.click
```

`LINE` is the line of `void __rb_insert(`. Each `expanded` row prints the
phase costs above.

### Rust chunks CI reproduction

On PR #268 at `4a3943de0`, the `unit, 2/4` shard of workflow
[37473480380](https://github.com/clicklang/click/actions/runs/37473480380)
failed in `rust_chunks_exact_owned_loop_tools_recheck_all_sites`. Its
`cover.contract` audit discovered 14 sites, initialized the retained session
in 2,057,595 work units and 21 seconds, then exhausted its ten-minute
whole-run bound while processing the claim. No proof failure was reported.

The saved import reproduces the slow capture workload without Charon:

```sh
click audit --time-limit 2m examples/rust-chunks-exact/chunks.click
```

At `4a3943de0`, this bounded local run initialized in 2,057,595 units and
11 seconds, reached eight of the fourteen sites, and stopped at the run
bound. The audit and its verifier workers exited. Keep this fixture’s C/Rust
source and contracts unchanged; fix the repeated capture work rather than
raising its time limit.

## Intended regression

A deterministic scaling regression that audits a claim with `n` independent
smart sites after a fixed prefix, at several `n`, and asserts the audit's
total counted work grows near linearly in `n` rather than with `n` times the
claim.

## Acceptance criteria

- Auditing one site of a claim costs work proportional to that site and the
  proof state it touches, not the whole claim's verification.
- `click audit examples/rbtree-insert` completes within its default limits.
- `scripts/check.sh` passes.
