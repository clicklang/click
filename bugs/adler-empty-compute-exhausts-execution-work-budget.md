# Empty Adler computation exhausts the execution work budget

The retained empty-input Adler32 proof reaches its deterministic execution
budget before finishing `execute_until(assignment(b, 3))`. This is forward
execution of an existing supported Rust fixture, not a new proof search
request. Preserve the existing implementation, proof, and budgets when fixing
the excessive work.

Reproduce with the pinned Charon runtime configured:

```sh
CLICK_NIGHTLY=1 cargo nextest run --profile nightly --run-ignored all \
  --test rust_import \
  -E 'test(=adler2_helpers::charon_adler2_empty_compute_proves_original_body_and_rejects_false_outputs)'
```

The fixture is `design/charon-trial/adler2/`; its test and sealed-project
setup are in `tests/rust_import/adler2_helpers.rs`. The failure is in
`__rust_q_I6_adler2_I4_algo_T29___rust_q_I6_adler2_I7_Adler32_I7_compute.contract`,
source tactic 3, statement 337: 2,000,001 smart work units exceed the unchanged
2,000,000-unit limit. It reproduces after the wide-arithmetic literal/snapshot
fix; that fix's focused checks pass. Wall time was about 44 seconds in an
isolated local run. The same obligation failed in nightly run 38059800813.

`click profile design/charon-trial/adler2/helpers.click` reproduces the same
work-budget failure. A stable local profile spent approximately 17 seconds in
the failing execution tactic; frontend and environment construction took only
4 and 7 milliseconds. The failing tactic's completed operation attribution
includes 496,501 units in assignments, 80,743 in call assignment, and 26,897
in verified-call requirement checking. These overlapping operation counts
locate work; they are not an additive accounting of the full tactic budget.

Reduce the expensive execution before changing the representation. Acceptance:
the original empty-input proof and its
existing false-output checks pass within the existing deterministic budgets;
proof tools agree; any representation change has deterministic scaling
regressions at multiple sizes. Do not raise limits or rewrite the original
Rust program or otherwise-correct proof to avoid the expensive execution.
