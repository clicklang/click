# Auditing a large claim re-verifies the whole claim for every site

## Violated invariant

A tool's cost must scale with the selected syntax and the output it produces
(`AGENTS.md`, "Scalable verification is a correctness requirement").
`click audit` instead costs the number of smart sites in a claim times the
cost of verifying that whole claim, twice over.

For each site the audit expands the site, which runs the whole claim with
capture, and then verifies the rewritten claim in its retained session, which
runs the whole claim again. `__rb_insert.contract` in
`examples/rbtree-insert/rbtree_insert.click` has 190 smart sites and takes
about 16 million work units to verify. Measured on a release build, every
site costs the same whatever it is:

| phase | work units | wall time |
| --- | --- | --- |
| expand one site | 17.2 million | 34 s |
| verify the rewrite in the session | 15.2 million | 32 s |
| re-expand | 1.6 million | 1 s |

That is about 67 seconds a site, so about 3.5 hours for the claim, past the
audit's own 110-minute run limit. The first site of a claim also runs two
cold verifications, about 32 seconds each. The audit of this example has
never been seen to complete.

Memory is no longer part of this. The retained session used to keep every
check's kernel state, about 1.1 GB a site here, which exhausted a 31 GB
machine. It now restores its baseline before each check and holds steady
near 8 GB (`retained_session_checks_leave_no_kernel_state_behind`). An
earlier version of this report blamed a single expansion allocating without
bound; that was the session's 5 GB plus one expansion's 5.5 GB meeting an
8 GB cap.

## Reproduction

Under a memory cap, on a release build:

```sh
cd examples
systemd-run --user --scope -q -p MemoryMax=14G -p MemorySwapMax=0 \
    ../target/release/click audit --verbose \
    --start-at rbtree-insert/rbtree_insert.click:LINE:1 \
    rbtree-insert/rbtree_insert.click
```

`LINE` is the line of `void __rb_insert(`. Each `ok` row prints the phase
costs above.

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
