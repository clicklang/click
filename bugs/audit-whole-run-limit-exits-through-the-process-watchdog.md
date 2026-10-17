# `click audit`'s whole-run limit exits through the process watchdog

Soundness: not soundness. This is a tooling diagnostic defect: a run that
reaches its whole-run wall-clock limit is killed instead of stopping at a
resumable cursor. No verdict about a proof changes.

## Violated invariant

`click audit --help` says the phase time limits are crash-containment bounds
for a hung run, and that `--time-limit` (default `10m`) is the whole-run wall
clock that "prints the resume cursor". When an audit reaches the whole-run
limit in the middle of a phase, the CLI instead prints

```text
click: stopped by wall-clock crash-containment bound after 724ms
```

and exits 1 with no `SUMMARY` and no `RESUME` command. The duration is the
time that remained before the whole-run deadline when the phase started, not
a limit the user set. A healthy, CPU-bound run therefore reads as a hung one.

## Cause

`PhaseLimit::within` caps each phase's time at the remainder of the whole-run
deadline (`remaining_phase_limit` in `src/bin/click-audit.rs`). `run_phase`
passes that capped value to `cli::within_run_limits`, which arms the
noncooperative `ProcessWatchdog` (`src/cli.rs`) with it as well as the
cooperative deadline. Near the deadline, the watchdog fires before the phase
reaches a cooperative checkpoint, and it calls `std::process::exit(1)` before
the audit loop's `Instant::now() >= deadline` check can print the cursor.

## Reproduction

At `66c9a207b` (branch `claude/rbtree-augmented-unfiled`), a release build,
on a 4-CPU machine:

```console
click audit --keep-going examples/rbtree-augmented
```

The run takes about 13 minutes (791 s measured with `--time-limit 90m`, which
completes with `SUMMARY: 482 sites passed; 0 site failures; 0 claim
failures; 2 session failures`). With the default `--time-limit 10m` it stops
twice in a row, at claims 72 and 68 of 101, with the message above and
neither summary nor cursor.

A quicker reproduction is a whole-run limit shorter than the first phase:
`click audit --keep-going --time-limit 20s examples/rbtree-augmented` prints
`INVENTORY` and then `click: stopped by wall-clock crash-containment bound
after 19.751s`. With `--time-limit 45s` the inventory finishes and the run
stops as intended: `RESUME:` with the command, then `click: audit stopped at
its 45s wall-clock run bound after 0 of 502 selected sites`.

## Acceptance

- Reaching `--time-limit` stops at a phase boundary or cooperative checkpoint
  and prints the `RESUME` command with an inclusive `--start-at`, and the
  summary of what was audited so far.
- The process watchdog stays the backup for a phase that is actually hung:
  its bound is the configured phase limit (or a fixed margin above the
  cooperative deadline), not the remainder of the whole-run deadline.
- A CLI regression with a short `--time-limit` checks for the cursor and
  for the absence of the crash-containment message.
