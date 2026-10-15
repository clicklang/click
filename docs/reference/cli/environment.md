# Environment variables

Click's ordinary user workflow does not require environment variables. The
variables on this page configure the version launcher, enable diagnostics,
select fixtures, or control contributor experiments.

## Launcher variables

These variables configure the `click` launcher and the
[version manager commands](versions.md).

### `CLICK_HOME`

Set `CLICK_HOME=DIR` to keep the launcher, installed versions, and the global
default under `DIR`. When it is unset or empty, Click uses `.click` under
`HOME`, or under `USERPROFILE` when `HOME` is unset. The installers read the
same variable.

### `CLICK_NO_VERSION_DISPATCH`

Set `CLICK_NO_VERSION_DISPATCH` to any value to make `click` run the command
itself instead of dispatching to a pinned or default version. The launcher
sets it to `1` for the version it dispatches to.

### `CLICK_RELEASE_REPOSITORY`

Set `CLICK_RELEASE_REPOSITORY=OWNER/NAME` to make `click install` download
releases, and resolve `latest`, from that GitHub repository instead of
`clicklang/click`. Each part may contain ASCII letters, digits, `-`, `_`, and
`.`; any other value fails.

## Front-end variables

### `CLICK_CHARON`

`click import lock` reads `CLICK_CHARON=PATH` when it prepares a Rust unit of a
project ([Project units](import.md#project-units)): the pinned `charon`
executable, with `charon-driver` beside it. Verification never reads it.

### `CLICK_CPP_EXPORTER`

`click import lock` reads `CLICK_CPP_EXPORTER=PATH`, the pinned C++ exporter,
when it prepares a C++ unit of a project. The test harnesses read it too.
Verification never reads it.

## Diagnostic variables

### `CLICK_TIMINGS`

Set `CLICK_TIMINGS=1` to emit per-tactic and verification-phase timing lines.
Prefer `click profile` for a reconciled report.

### `CLICK_TIMING_STARTS`

Set `CLICK_TIMING_STARTS=1` to emit internal timing-start events for engine
diagnostics.

### `CLICK_FULL_DIAGNOSTICS`

Set `CLICK_FULL_DIAGNOSTICS=1` to disable bounded diagnostic rendering and
expose full internal state. Use this variable only for reduction and engine
investigation.

Normal diagnostics deliberately bound internal terms. Do not recommend
`CLICK_FULL_DIAGNOSTICS` as a workaround for an enormous default diagnostic;
fix the bounded diagnostic instead.

## Fixture selection

### `MDTEST_FILTER`

Set `MDTEST_FILTER=TEXT` to run mdtests whose filename contains `TEXT`.

### `CLICK_EXAMPLE`

Set `CLICK_EXAMPLE=NAME` to run the named example project.

### `CLICK_RUN_QUARANTINED`

Set `CLICK_RUN_QUARANTINED=1` to include quarantined mdtests or examples. An
explicit filter also selects its matching quarantined fixture.

### `CLICK_TACTIC_WORK_REPORT`

Set `CLICK_TACTIC_WORK_REPORT=DIR` to have the mdtest and example harnesses
write the deterministic work every tactic charged, one tab-separated file per
fixture, into `DIR`. `scripts/measure-tactic-work.sh` sets it together with
`CLICK_DISABLE_TACTIC_BUDGETS=1` to calibrate the tactic work budgets; see
[Testing Click](../../internals/testing.md).

`scripts/check.sh` and the fixture harnesses also read `CLICK_NIGHTLY`,
`MDTEST_PARTITION`, `EXAMPLE_PARTITION`, `CLICK_REQUIRE_FRONTENDS`, and
`CLICK_CPP_EXPORTER`. [Testing Click](../../internals/testing.md) documents
them with the gate they configure.

## Contributor A/B controls

### `CLICK_DISABLE_TACTIC_BUDGETS`

Set `CLICK_DISABLE_TACTIC_BUDGETS=1` to disable per-tactic budget enforcement
for reduction and archaeology. The command's whole-run work budget and its
crash-containment bound still apply.

This variable is an internal experiment handle, not a stable user feature.
Use it only for an A/B regression that names the expected invariant. The
kernel reads no environment variable: its behaviour is fixed, and its
test-only audits are switched on by the tests that run them.
