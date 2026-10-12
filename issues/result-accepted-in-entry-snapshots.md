# `result` is accepted inside `old(...)` and `at(function.entry, ...)`

Priority: P2.

Soundness: soundness-adjacent. A meaningless claim is accepted with a
Click-specific meaning. `result` is rigid on the path, so
`at(function.entry, result == e)` means `result == e` with `e` evaluated at
entry. No false acceptance is known. On 2026-10-12 the following were tried.
`ensures at(function.entry, result == x)` for `x = 5; return x;` was refused.
A multi-path `ensures at(function.entry, result == 5)` was refused on the
path returning 6. A `have at(function.entry, result == 5)` before `execute()`
was refused ("unknown old-state variable `result`"). A caller cannot use a
contract that contains such a clause ("its contract refers to an internal
program point that is unavailable at the call site"). `ensures old(result) ==
5` now fails contract certification, with a misleading "exact symbolic
execution did not establish every contract claim" message instead of a
validation error.

## Violated invariant

A snapshot expression must only name state that exists at that snapshot.
`result` is the function's return value and does not exist at function entry,
so `old(result)` and `at(function.entry, result == 5)` have no meaning. The
surface accepts both today and treats `result` as snapshot-invariant, so the
proposition silently means the same as the unlabelled one.

The cost is in the tooling: the expander's snapshot-transport
closure (`try_snapshot_transport_closure` in
`src/surface/proof/smart_closures.rs`) tries `at(function.entry, goal)` first
and therefore emits a misleading no-op transport from function entry, wrapped
in a `have` plus `assumption`, where a direct closer would do.

## Reproduction

```c
int h(int x) { x = 5; return x; }
```

the sidecar contract `ensures at(function.entry, result == 5);` proved by
`execute(); simp();` verifies, and so does
`have at(function.entry, result == 5) by { simp(); }` after `execute()` in
a proof of `h`. `ensures old(result) == 5;` is refused only at contract
certification, with a message that does not name the snapshot.
Expanding the round trip in `mdtests/byte_representation_roundtrip.md` shows
the effect: every failure arm discharges the claim with
`transport(at(function.entry, result == 18 or result == -1), ...)`.

## Intended regression

The surface rejects `result` under `old(...)` and under any `at(<label>, ...)`
whose label precedes the return, with a diagnostic naming the snapshot and the
reason. The expander no longer offers an entry-labelled transport for a goal
that mentions `result`, and the expanded round trip's failure arms close the
claim directly. Two mdtests pin the rejections, and the round-trip expansion
fixture pins the absence of the entry transport.

## Acceptance criteria

- `old(result)` and `at(function.entry, result ...)` are refused at validation
  with an actionable message; existing fixtures that never used them are
  unaffected.
- Expanded proofs of functions with early-return arms do not contain
  entry-labelled transports of goals about `result`.
- `scripts/check.sh` passes. Delete this issue and its list entry when the
  rejection, the expander change, and their regressions land.
