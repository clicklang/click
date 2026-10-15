# Pointer-field reload loses backing-write authority


Priority: P2.

Soundness: incomplete. The recovery implementation rejects the second of two
in-bounds writes through the same descriptor field. This reproduction does not
demonstrate acceptance of a false claim. It is an archive compatibility defect,
not a claim that current upstream rejects the program.

Recovery checkpoint `c6d5c4200` rejects the second `step()` below. This preserves
the pointer-field reload pattern in `owned_string_push.c`, but uses constant
indices to remove loop and index-arithmetic explanations.

```c filename=probe.c
struct owner { int32 len; int32 cap; int32* data; };
int32 probe(struct owner* owner, int32 index, int32 value) {
    owner->data[0] = value;
    owner->data[1] = 0;
    return value;
}
```

```click
verifying "probe.c";
resource buffer(owner: struct owner*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len < owner->cap;
    fact separate(memory(*owner), memory(owner->data[0..owner->cap]));
}
int32 probe(struct owner* owner, int32 index, int32 value) {
    requires 0 <= index;
    requires index < owner->len;
    requires 2 <= owner->cap;
    owns buffer(owner);
    ensures result == value;
    ensures owner->data[0] == value;
} by {
    unfold(buffer(owner));
    step();
    step();
    have separate(memory(*owner), memory(owner->data[0..owner->cap])) by { simp(); }
    fold(buffer(owner));
    step();
    assumption();
    assumption();
    assumption();
}
```

## Observed boundary

Run `click verify --trace-proof probe <this-file>` with the recovery verifier.
The first write checks; `owner->data[1] = 0` reports missing write ownership.
The diagnostic tries to cover the backing address using `owns *owner`, while
the trace still shows the separate backing ownership and descriptor/backing
separation established by unfolding `buffer`. The reduced example deliberately
retains the original postcondition proof; its rejection occurs before that proof.

Checkpoint `c6d5c4200` separately repairs interior resource lookup through a
producer-registered pointer read's checked endpoint. Its kernel regression passes
with retained ownership, and rejects absent separation, withdrawn ownership,
out-of-bounds writes and partial pointer overwrites. That repair **does not**
restore this C example. Locate the additional lost read/authority evidence at
the execution boundary before broadening pointer-origin or designation rules.

The existing [pointer-field postcondition report](c-pointer-field-postconditions-lose-frame-evidence.md)
tracks the distinct stored-value/frame postconditions that still fail in the
unchanged string and vector projects. In a diagnostic reduction of the single
store, an explicit `have owner->data[index] == value by { simp(); }` checks;
`assumption` alone does not derive that equality. This does not establish that
the entire projects need only a proof adjustment.

## Acceptance

- Admit both writes with unchanged C and postconditions; restore the relevant
  original string/vector paths before claiming project compatibility.
- Check fresh verification, expansion, rewritten verification and retained
  rechecking of the repaired positive proof.
- Reject a wrong stored value, a partial pointer overwrite, missing backing
  ownership, missing required separation and an out-of-bounds second write.
- Preserve producer identity and checked full-pointer framing. Numeric address
  equality must not supply object designation or lifetime validity.
- Keep existing proof budgets and selected-query scaling beside unrelated state.
