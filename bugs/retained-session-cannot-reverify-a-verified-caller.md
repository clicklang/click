# A retained verification session cannot re-verify a caller it already verified

## Violated invariant

Verifying a proof unit must give the same verdict whether it is the first
verification on a thread or a later one sharing that thread's kernel tables.
`C0VerificationSession` in `src/surface/verification.rs` keeps the kernel
tables of its baseline run (`kernel::VerificationSession::resume`) so that
`verify_at` can re-check one proof unit cheaply; `click audit` uses it for
the first verification pass of every rewrite.

For a caller whose callee's precondition reads memory, the second
verification refuses a proof the first accepted. In
`mdtests/static_local_arrays.md`, `call_twice` calls `increment_twice()`
twice. After the baseline run, `session.verify_at` on the **unchanged**
source fails at the second call:

```
`call_twice.ensures_0` tactic 0: `execute()` is missing prerequisite (increment_twice precondition): ...
  C statement at static_local_arrays.c:12:5: `second = increment_twice();`
```

`click verify`, whole-file or targeted at that proof unit, accepts the same
source. The failure direction is a refused proof, never a wrongly accepted
one. This file was first filed as an expansion defect ("expansion loses the
facts a later call precondition needs"); the expansion is not involved.

## What is known

- The ordinary fresh targeted entry (`verify_c0_sources_at`) fails the same
  way when run inside the tables a previous verification left on the thread,
  so the surface session logic is not the cause.
- Passing no cached callee environment makes no difference.
- Clearing each of the other per-session kernel tables that
  `VerificationSession::enter` clears, singly or all together, makes no
  difference. Resetting the pure-function definitions makes no difference.
- Starting a fresh memory arena (`primitives::start_fresh_c_memory_arena`)
  alone makes the second verification pass.

So the cause is the memory arena being reused across two verifications of one
function. The arena interns snapshots by content and
`record_c_memory_derivation` is first-wins, so the second run's snapshots
pick up records the first run made. Which record matters, and why it blocks
the precondition, is not established. The kernel documents this hazard on
`VerificationSession`, which is why a fresh verification starts a new arena.

## Affected fixtures

Each verifies, and fails `click audit` in the retained session's pass:

- `mdtests/static_array_parity_fixed_multidimensional.md`
- `mdtests/static_array_parity_multidimensional.md`
- `mdtests/static_array_parity_scalar.md`
- `mdtests/static_local_arrays.md`
- `mdtests/static_local_array_requirement_stated_explicitly.md`
- `mdtests/cstr_dynamic_indexed_read.md`
- `mdtests/cstr_source_identity_reordered_requirement.md`

Only `static_local_arrays` was investigated. The two `cstr` fixtures fail on
the `strlen` precondition and may have another cause; split this file if so.

## Intended regression

A unit test that builds a `C0VerificationSession` for a reduced
`static_local_arrays` (a callee with a precondition over a static array's
elements, called twice) and asserts `session.verify_at` accepts the
unchanged caller. It fails today. Add the same check for a caller that is
verified twice through the fresh entry inside one resumed kernel session.

## Acceptance criteria

- A retained session re-verifies any proof unit of its baseline with the
  baseline's verdict, without discarding the tables that make it cheaper
  than a fresh run for the units it did not change.
- The fix states which arena record was stale and why first-wins recording
  was wrong for it; it does not weaken the cycle-freedom argument
  `record_c_memory_derivation` documents.
- `click audit` passes on the fixtures above (or the `cstr` ones are split
  out with their own cause), and `scripts/check.sh` passes.
