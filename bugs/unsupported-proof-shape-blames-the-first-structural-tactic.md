# Unsupported proof shape blames the first structural tactic

Soundness: incomplete. The proof is refused with a misleading message;
nothing false is accepted.

When no checked execution driver accepts a written function-claim script,
`unsupported_proof_shape` (`src/surface/proof/claim_proofs.rs`) reports
"the proof script is valid, but the verifier cannot yet certify it ... It
reached tactic N (SHAPE), which is not implemented in this execution
context". `proof_shape_hint` picks tactic `N` as the first structural tactic
in the script, not the tactic a driver declined. A `have` written before a
trailing `auto()` is therefore named as the unimplemented shape, although
the same `have` followed by `execute()` verifies. The message gives no goal,
so the [tracing procedure](../docs/concepts/tracing.md) cannot start from it
(its outcome 2), and the suggested rewrites (`outcomes`, `have proposition by
{ ... }`) do not apply.

```c filename=m.c
int area(int w, int h) { return w * h; }
int frame(int w, int h) {
    int inner = area(w, h);
    return inner + 1;
}
```

```click
verifying "m.c";

int32 area(int32 w, int32 h) {
    requires w >= 0 and w <= 1000;
    requires h >= 0 and h <= 1000;
    ensures result == w * h;
}

int32 frame(int32 w, int32 h) {
    requires w >= 0 and w <= 1000;
    requires h >= 0 and h <= 1000;
    ensures result == w * h + 1 by {
        step(); step();
        have w * h <= 1000000 by auto();
        auto();
    }
}
```

`click verify` reports `It reached tactic 2 (nested `have`), which is not
implemented in this execution context`. Replacing the final `auto();` with
`execute();` or `step();` verifies. `step(); step(); auto();` with no `have`
reports "the supplied tactic sequence" instead, and `have 1 == 1 by auto();
auto();` blames tactic 0.

Acceptance criteria:

- The refusal names the tactic a driver actually declined (here, the trailing
  `auto()` at an execution frontier), or says that no single tactic is known,
  rather than guessing from the script's shape.
- The refusal does not call the script valid when the declined tactic is not
  supported at that point, and suggests the supported form (`execute()`).
- A regression mdtest preserves this script and its expected message.
