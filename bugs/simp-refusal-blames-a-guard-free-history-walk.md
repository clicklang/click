# A `simp` refusal blames a guard-free history walk for a premise-spelling miss

Soundness: not soundness. The defect is in the explanation of a refusal:
nothing false is accepted, and the refused proof is refused for a real reason.
The report hides that reason and names a different one.

## Violated invariant

A proof error leads with the exact requirement that was not established
([proof-failure triage](../docs/concepts/proof-failure-triage.md#explain-the-program-requirement-first)),
and diagnostics do not present internal state as the cause when it is not.
Here `simp` finds a derivation for the goal and refuses it because some of
its premises have no source spelling. The report does not say so. Its only
specific evidence is a memory-history walk that stops at a store, and that
walk runs without the context's facts. A reader, and the M3 investigation of
2026-10-16, reads it as the cause.

## Reproduction

`examples/label-build-flags/label.click` at `d86757df`, with the C unchanged
and one clause added to `label_copy`:

```click
import click::bytes;
...
uint64 label_copy(char* dst, const char* src) {
    views s: cstr_at(src, _);
    owns dst[0u64..32u64];
    requires separate(memory(dst[0u64..32u64]), memory(src[0u64..s.len + 1u64]));
    ensures s.len < 32u64 implies result == s.len;
    ensures 32u64 <= s.len implies result == 31u64;
    ensures dst[result] == '\0';
    ensures bytes::equal(dst, 0u64, src, 0u64, result);
} by {
    step();
    step();
    step();
    open(cstr_at(src, s.len)) {
        execute();
    }
}
```

`click verify --trace-proof label_copy label.click` refuses
`label_copy.ensures_3` with:

```text
goal: ∀bound A:CMachineInteger(UInt64). ((true is true ∧ uint64 <(bound A, result) is true) ⇒ ...)
memory-history check stops at snapshot#2:
  store: 1 bytes at address value#3
  read range checked: 1 bytes at address value#1
  supplemental history explanation: equality and ownership facts from the failed check are not used by this walk
```

The store is `dst[n] = '\0'` and the read is `dst[k]`. The report suggests
that the copied-bytes fact from `memcpy` cannot be carried past the store
because nothing shows `k != n`.

## What actually fails

Instrumenting the closer (env-gated probes, not committed) shows:

- `derive_forall_rule` finds the body derivation (`ForAllBody`) for the
  goal, with the guard `k < n` assumed. Its load comparisons cross the
  `dst[n]` store for both the `dst + k` and the `src + k` reads; the `src`
  side crosses by the existing `StoreGeneralDistinctness` rung.
- The derivation keeps 7 context premises. `resolve_simp_premises` spells
  only 6 in source form, and the typed atomic closer then refuses it. The
  three premises with no source spelling are:
  - `CResourceSeparate` of `dst[UInt64:0..32]` and `src[UInt64:0..s.len+1]`,
    the contract's own `requires separate(...)` clause in its lowered form;
  - `0 <= (int32)(uint32)n` and `(int32)(uint32)n < 32`, internal bounds on
    the local `n`.
- The quoted walk comes from the supplemental explanation
  (`resource_tracker::explain`). It runs with an empty fact context
  (probed: no condition facts), so it never sees the guard `k < n`. The
  walks the proof search ran under the guard crossed the store.

Disabling a prototype rule that frames such stores by an exact guard lookup
(`guard-bounded store separation`, approved as option (a) and then withheld)
changed no outcome: the derivation is found with or without it.

## Acceptance criteria

- When `simp` or `auto` finds a derivation and refuses it because premises
  have no source spelling, the error says so and names the unspelled
  premises (bounded, in Click or C syntax where possible).
- A supplemental history walk that ran without the failed check's facts is
  not shown as the place the check stopped, or it is labeled as a walk that
  does not reflect the proof context, in the primary message and the trace.
- Regression: an expected-failure mdtest that keeps the original pattern
  (`memcpy(dst, src, n); dst[n] = '\0';` with a `bytes::equal` postcondition)
  and pins the new diagnostic. It must not pin the guard-free walk.
- `design/borrowed-c-strings.md` step 4 is corrected: its third gap is
  premise spelling, not the frame across `dst[n]`.
