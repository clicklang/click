# Expected-failure mdtests stop the audit's runtime inventory

Soundness: not soundness. The repository audit stops on a deliberately invalid
negative fixture before checking any proof expansions. No false acceptance is
known.

The fresh nightly audit on `aec1aa773` stopped during `INVENTORY`:
<https://github.com/clicklang/click/actions/runs/38980440610/job/117239792200>.
The test job is independent of this early audit refusal.

This smaller command reproduces the same failure with exit status 1:

```sh
click audit mdtests/a_sidecar_conjunction_written_as_ampersands_names_and.md
```

```text
INVENTORY
click: line 4, column 22: Click writes conjunction as `and`, not `&&`
  error kind: syntax error
```

The fixture deliberately writes `&&` in a Click precondition and expects that
syntax error. `inventory_sites` and `implicit_auto_sites` already skip mdtests
whose expectation is `MdTestExpectation::FailContains`. However, `run_audit`
first loads every source and queries its thread runtime, without that
expectation check. This preliminary pass therefore parses an intentionally
invalid sidecar before either existing skip applies.

Acceptance: apply the expected-failure boundary before preparing or parsing a
negative fixture in the runtime inventory. The named command should succeed
with no proof sites, and a mixed directory should still audit its positive
fixtures. Keep the original negative test and its expected syntax error;
positive fixtures with invalid syntax must still fail the audit. Add focused
coverage for these boundaries, then confirm the whole-repository inventory can
progress beyond this fixture without running a full local nightly.
