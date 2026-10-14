# Split backing ranges fail to rejoin after field-preserving modular calls

Soundness: incomplete. Recovery checkpoint `53da27b58` rejects the supported C
proof below although the upstream-based `73cff194e` verifier accepts all three
proofs. No false acceptance is demonstrated. This is an archive compatibility
regression, not an unsupported C feature or a demonstrated contract defect.

Priority: P2. Blocks the affected object-model activation.

## Reproduction

The unchanged `owned-segmented-buffer` example fails its final fold after two
modular writes. This reduction retains both descriptor fields, both backing
ranges, and the helpers' explicit field-preservation postconditions. Each helper
writes only the first element of its own backing buffer.

```c filename=probe.c
struct owner {
    int32 first_len;
    int32 second_len;
    int32* first_data;
    int32* second_data;
};
void set_first(struct owner* owner) { owner->first_data[0] = 1; }
void set_second(struct owner* owner) { owner->second_data[0] = 2; }
void probe(struct owner* owner) { set_first(owner); set_second(owner); }
```
```click
verifying "probe.c";
resource buffers(owner: struct owner*) {
    owns owner->first_len;
    owns owner->second_len;
    owns owner->first_data;
    owns owner->second_data;
    owns owner->first_data[0..owner->first_len];
    owns owner->second_data[0..owner->second_len];
    fact 1 <= owner->first_len;
    fact 1 <= owner->second_len;
    fact separate(memory(*owner), memory(owner->first_data[0..owner->first_len]));
    fact separate(memory(*owner), memory(owner->second_data[0..owner->second_len]));
}
void set_first(struct owner* owner) {
    requires separate(memory(*owner), memory(owner->first_data[0..owner->first_len]));
    views owner->first_len;
    views owner->second_len;
    views owner->first_data;
    views owner->second_data;
    owns owner->first_data[0..1];
    ensures owner->first_len == old(owner->first_len);
    ensures owner->second_len == old(owner->second_len);
    ensures owner->first_data == old(owner->first_data);
    ensures owner->second_data == old(owner->second_data);
} by { execute(); simp(); }
void set_second(struct owner* owner) {
    requires separate(memory(*owner), memory(owner->second_data[0..owner->second_len]));
    views owner->first_len;
    views owner->second_len;
    views owner->first_data;
    views owner->second_data;
    owns owner->second_data[0..1];
    ensures owner->first_len == old(owner->first_len);
    ensures owner->second_len == old(owner->second_len);
    ensures owner->first_data == old(owner->first_data);
    ensures owner->second_data == old(owner->second_data);
} by { execute(); simp(); }
void probe(struct owner* owner) {
    owns buffers(owner);
} by {
    unfold(buffers(owner));
    step(); step();
    fold(buffers(owner));
    execute(); simp();
}
```
```expect
pass
```

## Observed evidence

Run `click verify --trace-proof probe <this-file>` with a freshly checked build.
On `53da27b58`, the last `fold` reports missing
`owns owner->second_data[0..owner->second_len]`, while the remaining holdings show
both `owns owner->second_data[0..1]` and
`owns owner->second_data[1..owner->second_len]`. The trace identifies the tail's
pointer read before either call and the prefix's read after the first call.
Numeric field-preservation equalities are recorded, but the range join does not
complete. The introducing change and missing checked framing/transport step
remain unattributed; numeric equality alone must not grant a pointer origin.

The full original recovery example stage still reports 39/52 passing on this
checkpoint, with the same 13 failed projects as `bd6659d9a`. The other buffer
fold failure is `owned-split-buffer`; a shared cause is not yet established.

## Acceptance

- Verify this unchanged C/proof fresh, after expansion, and in a retained session.
- Restore the original segmented-buffer pipeline; test the split-buffer failure
  independently before attributing it to this repair.
- Retain full-width, changed/partial-pointer-write, overlapping-range and
  withdrawn-authority rejection controls. Preserve pointer-origin checks.
- Bound selected proof work beside unrelated resources at multiple sizes. Keep
  existing tactic budgets, claims and source programs unchanged.
- Recheck the normal example stage and report any remaining failures separately.
