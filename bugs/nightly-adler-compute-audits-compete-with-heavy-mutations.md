# Nightly Adler compute audits time out while heavy mutations run concurrently

Nightly 38149193625 on `486e809747b79f223ffb2f38ace3034bae9b6491`
failed `charon_adler2_four_byte_compute_tools_recheck_original_contract`:
its audit stopped at the unchanged 600-second whole-run bound with 0/211 sites
completed. The four-byte body/mutation test and several general-compute body,
mutation, and tool tests ran concurrently in that job. General compute also
stopped at 0/765 sites. Focused runs of the four-byte test passed locally;
this is separate from the reproducible general-checker work and small-batch
rewrite defects.

Run the nightly Rust import suite with its ordinary parallelism and installed
Charon, retaining the original imported programs, contracts, work budgets,
and tool timeouts. The large compute audits must not compete with each other
and the corresponding large mutation families. Keep ordinary tests parallel.
The three compute tool regressions must pass without changing their proof
obligations or increasing their time limits.
